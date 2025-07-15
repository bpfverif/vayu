from dataclasses import dataclass, field
from typing import Callable
from component import *
import logging
import itertools
from spec_abs import abs_prog_spec_mappings, init_seed
import math
from datetime import datetime
import argparse
import sys
import parse_to_lambda
import enum
from program_builder import inject_prog, inject_prog_mappings


class CegisState(enum.Flag):
    INIT_POS = enum.auto()
    SYNTH_POS_NEG = enum.auto()
    SYNTH_NEW_NEG = enum.auto()
    VERIF_POS_NEG = enum.auto()
    VERIF_NEW_NEG = enum.auto()
    VALIDATE_NEG = enum.auto()


class Cegis:

    def __init__(
        self,
        conc_func_semantics,
        abs_wf_semantics,
        abs_contains_semantics,
        eg_generator_func,
        num_inputs,
        num_outputs,
        components,
        num_initial_inputs,
        log_to_file,
        log_to_console,
        stop_after_iter,
        enable_invalid_linenos_opt,
        enable_invalid_conns_opt,
        timeout,
        smt_filename,
        prog_to_inject,
    ):

        self.conc_func_semantics = conc_func_semantics
        self.abs_wf_semantics = abs_wf_semantics
        self.abs_contains_semantics = abs_contains_semantics
        self.example_generator_func = eg_generator_func
        self.num_inputs = num_inputs
        self.num_outputs = num_outputs
        self.stop_after_iter = stop_after_iter
        self.num_initial_inputs = num_initial_inputs
        self.curr_synthesized_program_str = ""
        self.positive_examples = set()
        self.negative_examples = set()
        self._init_logging(log_to_file, log_to_console)

        self.do_inject_prog = True if prog_to_inject else False
        self._init_component_library(
            components=components, prog_to_inject=prog_to_inject
        )

        self.sound_operators = set()
        self.unsound_operators = set()

        self.last_synthesized_lineno_assignment = {}
        self.enable_invalid_linenos_opt = enable_invalid_linenos_opt
        self.unsound_lineno_assignments = []

        self.enable_invalid_conns_opt = enable_invalid_conns_opt
        self._init_invalid_connections()

        self.timeout = timeout
        self.smt_filename = smt_filename

    def _reset_linenos(self):
        for component in self.component_library:
            component.reset_linenos()

    def _instantiate_linenos(self, context):
        for component in self.component_library:
            component._init_linenos(context)

    def _reset_instance_ids(self):
        for component in self.component_library:
            component.reset_instance_id()

    def _instantiate_new_input_output_params(self, context):
        for component in self.component_library:
            component.instantiate_new_input_output_params(context=context)

    def _get_prog_input_bvs(self, instance_id):
        prog_input_bvs = []
        for prog_input_component in self.prog_inputs:
            prog_input_bvs.extend(prog_input_component.get_param_out_bvs(instance_id))
        return prog_input_bvs

    def _get_prog_output_bvs(self, instance_id):
        prog_output_bvs = []
        for prog_output_component in self.prog_outputs:
            prog_output_bvs.extend(prog_output_component.get_param_out_bvs(instance_id))
        return prog_output_bvs

    def _init_logging(self, log_to_file, log_to_console):
        self.logger = logging.getLogger(__name__)
        datetime_str = datetime.now().strftime("%H_%M_%d_%m_%Y")
        self.logfile_name = datetime.now().strftime("log_{}.log".format(datetime_str))
        formatter = logging.Formatter("%(message)s")
        if log_to_file:
            fhandler = logging.FileHandler(self.logfile_name)
            fhandler.setFormatter(formatter)
            self.logger.addHandler(fhandler)
        if log_to_console:
            console_handler = logging.StreamHandler(sys.stdout)
            console_handler.setFormatter(formatter)
            self.logger.addHandler(console_handler)
        self.logger.setLevel(logging.DEBUG)

    def _init_component_library(self, components, prog_to_inject):
        """
        initialize component_library by instantiating components given to us
        in 'components'.
        also create new lineno bitvectors for each component
        """

        # if we are injecting a progarm into the cegis loop, we don't need to initialize
        # a component library, program_builder will do it for us
        if prog_to_inject:
            prog = inject_prog(prog_to_inject)
            self.component_library = prog.components
            self.prog_inputs = prog.var_inputs
            self.prog_outputs = prog.var_outputs
            self._update_synthesized_program_string()
            return

        # add input and output components to the given base library of components, based
        # on the to-be-synthesized program's arity
        for _ in range(0, self.num_inputs):
            components.insert(0, VarInputComponent)
        for _ in range(0, self.num_outputs):
            components.append(VarOutputComponent)

        # each component (including input and outputs) occur on a new line. decide what
        # is the bitwidth of the maximum line number
        Component.LINENO_BV_BITWIDTH = math.ceil(math.log2(len(components)))

        # initialize the components, and save the instances in self.component_library
        self.component_library = []
        for component in components:
            if isinstance(component, tuple):
                compInstance = component[0](const_value=component[1])
            else:
                compInstance = component()
            self.component_library.append(compInstance)

        # save the input and output components separately
        self.prog_inputs = [
            component
            for component in self.component_library
            if isinstance(component, VarInputComponent)
        ]
        self.prog_outputs = [
            component
            for component in self.component_library
            if isinstance(component, VarOutputComponent)
        ]

    def _init_invalid_connections(self):
        """
        this function helps us avoid adding unnecessary assertions to psiconn, where we
        make assertions of the form (lx == ly ==> Ox == Oy). if we know that lx == ly
        will never be true, we can avoid making these assertions in psiconn, to reduce
        the length of the formula. this function collects these invalid connections in
        self.invalid_connections list, and later get_psiconn uses this list to avoid
        asserting unnecessary connections.
        """
        self.invalid_connections = []

        if not self.enable_invalid_conns_opt:
            return

        prog_input_lineno_output_bvs = set()
        prog_output_lineno_output_bvs = set()
        for component in self.component_library:
            if isinstance(component, VarInputComponent):
                for output_lineno_bv in component.get_lineno_out_bvs():
                    prog_input_lineno_output_bvs.add(output_lineno_bv)
            if isinstance(component, VarOutputComponent):
                for output_lineno_bv in component.get_lineno_out_bvs():
                    prog_output_lineno_output_bvs.add(output_lineno_bv)

        # skip assigning program inputs directly to program outputs e.g. if program
        # input is O0 (lo0), and program output is O7 (lo7) skip asserting that (lo0 ==
        # lo7 ==> O0 == O7)
        prog_input_to_prog_output = list(
            itertools.product(
                prog_input_lineno_output_bvs, prog_output_lineno_output_bvs
            )
        )
        self.invalid_connections.extend(prog_input_to_prog_output)

        # skip assigning one program input to other program input e.g. if program inputs
        # are O0 (lo0), and O1 (lo1) skip asserting that (lo0 == lo1 ==> O0 == O1)
        prog_input_to_prog_input = list(
            itertools.combinations(prog_input_lineno_output_bvs, 2)
        )
        self.invalid_connections.extend(prog_input_to_prog_input)

        # skip assigning one program output to other program output e.g. if program
        # outputs are O7 (lo7), and O8 (lo8) skip asserting that (lo7 == lo8 ==> O7 ==
        # O8)
        prog_output_to_prog_output = list(
            itertools.combinations(prog_output_lineno_output_bvs, 2)
        )
        self.invalid_connections.extend(prog_output_to_prog_output)

        # skip assigning a component's input param location to the same component's
        # other input param location e.g. consider component O5 (lo5) := I50 (li50) ^
        # I51 (li51) skip asserting that (li50 == li51 ==> I50 == I51)
        input_param_to_input_param = []
        for component in self.component_library:
            if isinstance(component, VarInputComponent | VarOutputComponent):
                continue
            component_lineno_input_bvs = set()
            for input_lineno_bv in component.get_lineno_in_bvs():
                component_lineno_input_bvs.add(input_lineno_bv)
            input_param_to_input_param.extend(
                list(itertools.combinations(component_lineno_input_bvs, 2))
            )
        self.invalid_connections.extend(input_param_to_input_param)

        # skip assigning a component's output location to its input param locations,
        # because a component's output location will always be greater than its input
        # param locations e.g. consider component O5 (lo5) := I50 (li50) ^ I51 (li51)
        # skip the following assertions: (lo5 == li50 ==> O5 == I50), (lo5 == li51 ==>
        # O5 == I51)
        output_param_to_input_param = []
        for component in self.component_library:
            if isinstance(component, VarInputComponent | VarOutputComponent):
                continue
            output_param_to_input_param_i = list(
                itertools.product(
                    component.get_lineno_out_bvs(), component.get_lineno_in_bvs()
                )
            )
            output_param_to_input_param.extend(output_param_to_input_param_i)
        self.invalid_connections.extend(output_param_to_input_param)

    def get_initial_positive_examples(self):
        """
        initialize the starting set of concrete example inputs
        """
        while len(self.positive_examples) < self.num_initial_inputs:
            eg = self.example_generator_func()
            if eg in self.positive_examples:
                continue
            self.positive_examples.add(eg)

    def get_psicons(self, context):
        """
        assert that the output line number bitvectors of each component in our component
        library are different -- each component should appear on a different line. e.g.
        lo1 != lo2 AND lo2 != lo3, and so on
        """
        all_output_lineno_bvs = set()
        for component in self.component_library:
            for output_lineno_bv in component.get_lineno_out_bvs():
                all_output_lineno_bvs.add(output_lineno_bv)
        psicons = [
            i[0] != i[1] for i in list(itertools.combinations(all_output_lineno_bvs, 2))
        ]
        psicons = z3.Distinct(all_output_lineno_bvs)
        return psicons

    def get_psiacyc(self, context):
        """
        for every component, if x is input (with location lx), y is output (location ly,
        where ly is the component's final position) then lx should be earlier than ly
        """
        psiacyc = []
        for component in self.component_library:
            input_lineno_bvs = component.get_lineno_in_bvs()
            output_lineno_bvs = component.get_lineno_out_bvs()
            lineno_input_output_combinations = list(
                itertools.product(input_lineno_bvs, output_lineno_bvs)
            )
            for input_lineno, output_lineno in lineno_input_output_combinations:
                psiacyc.append(z3.ULT(input_lineno, output_lineno))
        return z3.And(psiacyc, context)

    def get_psibounds(self, context):
        """
        for all the "semantic" components, all input line numbers li are: 0 <= li <=
        num_inputs + num_components - 1 all output line numbers lo are: num_inputs < lo
        < self.num_inputs + num_components -1
        """

        all_lineno_input_bvs = set()
        all_lineno_output_bvs = set()
        for component in self.component_library:
            if isinstance(component, VarInputComponent | VarOutputComponent):
                continue
            for output_lineno_bv in component.get_lineno_out_bvs():
                all_lineno_output_bvs.add(output_lineno_bv)
            for input_lineno_bv in component.get_lineno_in_bvs():
                all_lineno_input_bvs.add(input_lineno_bv)

        prog_length = len(self.component_library) - self.num_outputs
        zero_lineno = z3.BitVecVal(0, Component.LINENO_BV_BITWIDTH, ctx=context)
        max_lineno = z3.BitVecVal(
            prog_length - 1, Component.LINENO_BV_BITWIDTH, ctx=context
        )

        psibounds_input = []
        psibounds_output = []
        for lineno_bv in all_lineno_input_bvs:
            psibounds_input.append(z3.ULE(zero_lineno, lineno_bv))
            psibounds_input.append(z3.ULE(lineno_bv, max_lineno))
        for lineno_bv in all_lineno_output_bvs:
            psibounds_output.append(z3.ULE(self.num_inputs, lineno_bv))
            psibounds_output.append(z3.ULE(lineno_bv, max_lineno))

        psibounds = psibounds_input + psibounds_output
        return z3.And(psibounds, context)

    def get_psiwfp(self, context):
        """
        psiwfp = psicons AND psiacyc AND psibounds
        """
        psicons = self.get_psicons(context=context)

        psiacyc = self.get_psiacyc(context=context)

        psibounds = self.get_psibounds(context=context)

        psiwfp = z3.And(psibounds, psicons, psiacyc, context)

        return psiwfp

    def get_unsound_lineno_assignments(self, context):
        """
        get a formula that corresponds to all the unsound programs, that we have saved
        in unsound_lineno_assignments. For e.g. let's say unsound_lineno_assignments =
        [{lo1:3, lo2: 2, lo1: 1}, {lo1:2, lo2: 3, lo1: 1}] Then the formula is: (lo1 !=
        3 OR lo2 != 2 OR lo1 != 1) AND (lo1 != 2 OR lo2 != 3 OR lo1 != 1). This formula
        explicitly forbids the particular combination of line numbers that correspond to
        each invalid program we have discovered and saved.
        """

        if not self.enable_invalid_linenos_opt:
            return z3.And([], context)

        formula = []
        for unsound_lineno_assignment in self.unsound_lineno_assignments:
            unsound_i = []
            for output_lineno_bv_str, invalid_lineno in unsound_lineno_assignment:
                output_lineno_bv = z3.BitVec(
                    output_lineno_bv_str, Component.LINENO_BV_BITWIDTH, ctx=context
                )
                unsound_i.append(output_lineno_bv == invalid_lineno)

            formula.append(z3.Not(z3.And(unsound_i, context), ctx=context))

        return z3.And(formula, context)

    def get_psiconn(self, instance_id, context):
        """
        connect the line number bitvectors, with the corresponding component bitvectors,
        e.g. Implies(lo1 == li11, O1 == I11) AND Implies(lo1 == li11, O1 == I11)
        """

        input_param_lineno_pairs = set()
        output_param_lineno_pairs = set()
        for component in self.component_library:
            input_params = component.get_param_in_bvs(instance_id)
            output_params = component.get_param_out_bvs(instance_id)
            input_param_lineno_pair = zip(input_params, component.input_linenos)
            output_param_lineno_pair = zip(output_params, component.output_linenos)
            input_param_lineno_pairs |= set([i for i in input_param_lineno_pair])
            output_param_lineno_pairs |= set([i for i in output_param_lineno_pair])

        all_param_lineno_pairs = input_param_lineno_pairs | output_param_lineno_pairs

        # Implies(lo1 == lo2, O1 == O2), and so on ...
        psiconn = []
        for comp0, comp1 in itertools.combinations(all_param_lineno_pairs, 2):
            param0, lineno0 = comp0[0], comp0[1]
            param1, lineno1 = comp1[0], comp1[1]
            if (lineno0, lineno1) in self.invalid_connections:
                continue
            if (lineno1, lineno0) in self.invalid_connections:
                continue
            psiconn.append(
                z3.Implies(lineno0 == lineno1, param0 == param1, ctx=context)
            )

        return z3.And(psiconn, context)

    def get_philib(self, instance_id, context):
        """
        get a formula representing all the components in our library. e.g. if our
        component library contains AndComponent, and OrComponent, this returns And(O1 ==
        I11 & I12, O2 == I21 | I22)
        """
        philib = []
        for component in self.component_library:
            if isinstance(component, VarInputComponent):
                continue
            philib.append(component.make_expr(instance_id))

        philib = z3.And(philib, context)
        return philib

    def _print_lineno_assignments(self):
        lineno_assignments_str = ""
        component_library_sorted_by_component_id = sorted(
            self.component_library, key=lambda x: x.component_id
        )

        for component in component_library_sorted_by_component_id:
            lineno_assignments_str += (
                f"{component.component_id}: "
                + f"<curr: {component.output_lineno_assignments}, {component.input_lineno_assignments}>, "
                + f"<old: {component.output_lineno_assignments}, {component.input_lineno_assignments}>"
                + "\n"
            )

        print(lineno_assignments_str)

    def _update_synthesized_program_string(self):
        """
        a string representation of the current synthesized program
        """

        # first sort the component library by output lineno assignments -- the component
        # with the smallest lineno assignment should come first in our program string.
        component_library_sorted = sorted(
            self.component_library, key=lambda x: x.output_lineno_assignments[0]
        )

        program_str = ""
        for component in component_library_sorted:
            program_str += (component.get_expr_str()) + "\n"

        self.curr_synthesized_program_str = program_str
        self.curr_synthesized_program_str_lambda = parse_to_lambda.construct_lambda(
            self.curr_synthesized_program_str, self.num_inputs, self.num_outputs
        )

    def _write_smt_to_file(self, smt2_str):
        """
        write the smt2 of the query to a file, along with the current list of positive
        and negative examples, and the current synthesized program as comments.
        """

        # obtain the current synthesized program string as a comment in smt2, i.e.,
        # prepended with ";"
        curr_synthesized_program_str_comment = "\n".join(
            f";{line}"
            for line in self.curr_synthesized_program_str.strip().splitlines()
        )
        with open(self.smt_filename, "w") as f:
            f.write(";")
            f.write(str(self.positive_examples))
            f.write("\n")
            f.write(";")
            f.write(str(self.negative_examples))
            f.write("\n")
            f.write(curr_synthesized_program_str_comment)
            f.write("\n")
            f.write(smt2_str)

    def _print_finite_synthesis_model(self, model):
        print("full finite synthesis model:")
        print(model)
        print("finite synthesis model (only input and output linenos):")
        for component in self.component_library:
            for lineno_in_bv in component.get_lineno_in_bvs():
                print(str(lineno_in_bv) + ":" + str(model[lineno_in_bv]))
            for lineno_out_bv in component.get_lineno_out_bvs():
                print(str(lineno_out_bv) + ":" + str(model[lineno_out_bv]))

    def _update_lineno_assignments_from_finite_synthesis_model(self, model):
        for component in self.component_library:
            component.update_lineno_assignments(model)

    def _restore_old_lineno_assignments(self):
        for component in self.component_library:
            component.restore_lineno_assignments()
        self._update_synthesized_program_string()

    def get_const_constraints(self, context):
        """
        all constants appear are fixed to the initial line numbers
        """

        const_constraints = []
        i = self.num_inputs
        for component in self.component_library:
            if not isinstance(component, (ConstComponent)):
                continue
            for lineno_bv in component.get_lineno_out_bvs():
                const_constraints.append(lineno_bv == i)
            i += 1

        return z3.And(const_constraints, context)

    def get_input_output_lineno_constraints(self, context):
        input_lineno_constraints = []
        # first input occurs on line 0, second one line 1, etc. lo00 == 0, lo01 == 1,
        # and so on
        for i, prog_input_i in enumerate(self.prog_inputs):
            for lineno_bv in prog_input_i.get_lineno_out_bvs():
                input_lineno_constraints.append(lineno_bv == i)
        input_lineno_constraints = z3.And(input_lineno_constraints, context)

        # first output occurs on line prog_length, second on prog_length + 1, etc. lox0
        # == N, loy0 = N + 1, and so on
        prog_length = len(self.component_library) - self.num_outputs
        output_lineno_constraints = []
        for i, prog_output_i in enumerate(self.prog_outputs, start=prog_length):
            for lineno_bv in prog_output_i.get_lineno_out_bvs():
                output_lineno_constraints.append(lineno_bv == i)
        output_lineno_constraints = z3.And(output_lineno_constraints, context)

        return z3.And(input_lineno_constraints, output_lineno_constraints, context)

    def get_all_lineno_constraints(self, context):

        lineno_constraints = []
        input_output_lineno_constraints = self.get_input_output_lineno_constraints(
            context=context
        )
        lineno_constraints.append(input_output_lineno_constraints)

        const_constraints = self.get_const_constraints(context)
        lineno_constraints.append(const_constraints)

        invalid_assignments = self.get_unsound_lineno_assignments(context=context)
        lineno_constraints.append(invalid_assignments)

        psiwfp = self.get_psiwfp(context=context)
        lineno_constraints.append(psiwfp)

        return z3.And(lineno_constraints, context)

    def get_works_for_example_constraint(
        self, eg_input, eg_output, instance_id, context
    ):
        """
        the program should work for example input, in that the input bitvectors are
        equal to the examples e.g. if current example is: (129, 34, 67, 52): 247 then we
        assert that inputabs0 == 129 AND inputabs1 == 24 AND inputabs2 == 64 AND
        inputabs3 == 5 AND outputconc == 247 AND outputconc IN (outputabs0,
        outputabs1).
        """

        spec_works_for_inputs = []
        for i in range(0, self.num_inputs):
            prog_input_i = self.prog_inputs[i]
            prog_input_param_i = prog_input_i.get_param_out_bvs(
                instance_id=instance_id
            )[-1]
            spec_works_for_inputs.append(prog_input_param_i == eg_input[i])
        spec_works_for_inputs = z3.And(spec_works_for_inputs, context)

        prog_output_bvs = self._get_prog_output_bvs(instance_id=instance_id)

        spec_output_contains = self.abs_contains_semantics(eg_output, *prog_output_bvs)
        spec_output_wf = self.abs_wf_semantics(*prog_output_bvs)

        works_for_example = z3.And(
            spec_works_for_inputs, spec_output_contains, spec_output_wf, context
        )

        return works_for_example

    def get_does_not_work_for_example_constraint(
        self, eg_input, eg_output, instance_id, context
    ):
        """
        similar to above, but the example outputconc is NOTIN the abstract output.
        """
        spec_does_not_work_for_inputs = []
        for i in range(0, self.num_inputs):
            prog_input_i = self.prog_inputs[i]
            prog_input_param_i = prog_input_i.get_param_out_bvs(
                instance_id=instance_id
            )[-1]
            spec_does_not_work_for_inputs.append(prog_input_param_i == eg_input[i])
        spec_does_not_work_for_inputs = z3.And(spec_does_not_work_for_inputs, context)

        prog_output_bvs = self._get_prog_output_bvs(instance_id=instance_id)
        spec_output_does_not_contain = z3.Not(
            self.abs_contains_semantics(eg_output, *prog_output_bvs), ctx=context
        )
        spec_output_wf = self.abs_wf_semantics(*prog_output_bvs)

        does_not_work_for_example = z3.And(
            spec_does_not_work_for_inputs,
            spec_output_does_not_contain,
            spec_output_wf,
            context,
        )

        return does_not_work_for_example

    def get_works_for_positive_negative_examples_constraint(self, context):

        works_for_positive_negative_examples_formula = []

        for pos_eg in self.positive_examples:
            abs_input = pos_eg[0 : self.num_inputs]
            conc_output = pos_eg[self.num_inputs]

            self._instantiate_new_input_output_params(context=context)

            psiconn = self.get_psiconn(instance_id=-1, context=context)
            works_for_positive_negative_examples_formula.append(psiconn)

            philib = self.get_philib(instance_id=-1, context=context)
            works_for_positive_negative_examples_formula.append(philib)

            works_for_example = self.get_works_for_example_constraint(
                eg_input=abs_input,
                eg_output=conc_output,
                instance_id=-1,
                context=context,
            )
            works_for_positive_negative_examples_formula.append(works_for_example)

        for neg_eg in self.negative_examples:
            abs_input = neg_eg[0 : self.num_inputs]
            conc_output = neg_eg[self.num_inputs]

            self._instantiate_new_input_output_params(context=context)

            psiconn = self.get_psiconn(instance_id=-1, context=context)
            works_for_positive_negative_examples_formula.append(psiconn)

            philib = self.get_philib(instance_id=-1, context=context)
            works_for_positive_negative_examples_formula.append(philib)

            does_not_work_for_example = self.get_does_not_work_for_example_constraint(
                eg_input=abs_input,
                eg_output=conc_output,
                instance_id=-1,
                context=context,
            )
            works_for_positive_negative_examples_formula.append(
                does_not_work_for_example
            )

        return z3.And(works_for_positive_negative_examples_formula, context)

    def finite_synthesis_positive_negative(self):
        """
        attempt to synthesize a program that works for current input examples. on
        success, return with components in component_library updated with their lineno
        assignments.
        """
        context = z3.Context()
        solver = z3.Solver(ctx=context)
        solver.set("timeout", self.timeout)

        self._reset_linenos()
        self._instantiate_linenos(context=context)
        self._reset_instance_ids()

        lineno_constraints = self.get_all_lineno_constraints(context=context)
        solver.add(lineno_constraints)

        works_for_examples = self.get_works_for_positive_negative_examples_constraint(
            context=context
        )
        solver.add(works_for_examples)

        smt2_str = solver.to_smt2()
        if self.smt_filename:
            self._write_smt_to_file(smt2_str)

        issat = solver.check()

        stats = solver.statistics()
        try:
            time = stats.get_key_value("time")
            print("solver time (secs): ", time)
        except z3.Z3Exception as e:
            pass

        if str(issat) == "sat":

            # solver returned a model -- we have a candidate program
            synthesis_model = solver.model()

            # save the lineno assignnments in last_synthesized_lineno_assignment: if
            # they correspond to an invalid program after verify(), we will explicitly
            # forbid them; currently, these are saved as a dictionary of *strings* to
            # *ints* e.g.: {'lo7': 4, 'lo8': 7, 'lo9': 9, 'lo5': 6), 'lo4': 8, 'lo6':
            # 5}.
            all_lineno_bvs = set()
            for component in self.component_library:
                if isinstance(component, (VarInputComponent)):
                    continue
                if isinstance(component, (VarOutputComponent)):
                    continue
                for lineno_bv in component.get_lineno_out_bvs():
                    all_lineno_bvs.add(lineno_bv)
                for input_lineno_bv in component.get_lineno_in_bvs():
                    all_lineno_bvs.add(input_lineno_bv)

            for lineno_bv in all_lineno_bvs:
                self.last_synthesized_lineno_assignment[str(lineno_bv)] = (
                    synthesis_model[lineno_bv].as_long()
                )

            # self._print_finite_synthesis_model(model=synthesis_model)
            self._update_lineno_assignments_from_finite_synthesis_model(
                model=synthesis_model
            )
            self._update_synthesized_program_string()

            del context
            del solver
            z3.Z3_reset_memory()

        elif str(issat) == "unknown":

            # solver returned unknown, cannot proceed
            reason_unknown = str(solver.reason_unknown())

            del context
            del solver
            z3.Z3_reset_memory()

            raise RuntimeError(f"synthesis failed: {reason_unknown}")

        elif str(issat) == "unsat":

            # solver returned unsat, we cannot proceed
            unsat_core = str(solver.unsat_core())

            del context
            del solver
            z3.Z3_reset_memory()

            raise RuntimeError(f"synthesis failed.")

    def get_new_prog_excludes_neg_eg_constraint(
        self, new_neg_conc_out, new_neg_abs_in_lst, context
    ):

        self._instantiate_new_input_output_params(context=context)

        new_neg_abs0_in, new_neg_abs1_in, new_neg_abs2_in, new_neg_abs3_in = (
            new_neg_abs_in_lst
        )

        new_prog_excludes_eg_constraint = []

        new_prog_excludes_eg_constraint.append(
            self.abs_wf_semantics(new_neg_abs0_in, new_neg_abs1_in)
        )
        new_prog_excludes_eg_constraint.append(
            self.abs_wf_semantics(new_neg_abs2_in, new_neg_abs3_in)
        )

        psiconn = self.get_psiconn(instance_id=-1, context=context)
        new_prog_excludes_eg_constraint.append(psiconn)

        philib = self.get_philib(instance_id=-1, context=context)
        new_prog_excludes_eg_constraint.append(philib)

        new_prog_input_bvs = self._get_prog_input_bvs(instance_id=-1)
        new_prog_output_bvs = self._get_prog_output_bvs(instance_id=-1)

        for i in zip(new_prog_input_bvs, new_neg_abs_in_lst):
            new_prog_excludes_eg_constraint.append(i[0] == i[1])
        new_prog_excludes_eg_constraint.append(
            z3.Not(
                self.abs_contains_semantics(new_neg_conc_out, *new_prog_output_bvs),
                ctx=context,
            )
        )
        new_prog_excludes_eg_constraint.append(
            self.abs_wf_semantics(*new_prog_output_bvs)
        )

        return z3.And(new_prog_excludes_eg_constraint, context)

    def get_curr_prog_includes_neg_eg_constraint(
        self, new_neg_conc_out, new_neg_abs_in_lst, context
    ):
        self._instantiate_new_input_output_params(context=context)

        curr_prog_excludes_eg_constraint = []

        curr_prog = self.construct_prog(instance_id=-1, context=context)
        curr_prog_input_bvs = self._get_prog_input_bvs(instance_id=-1)
        curr_prog_output_bvs = self._get_prog_output_bvs(instance_id=-1)

        curr_prog_excludes_eg_constraint.append(curr_prog)

        for i in zip(curr_prog_input_bvs, new_neg_abs_in_lst):
            curr_prog_excludes_eg_constraint.append(i[0] == i[1])
        curr_prog_excludes_eg_constraint.append(
            self.abs_contains_semantics(new_neg_conc_out, *curr_prog_output_bvs)
        )
        curr_prog_excludes_eg_constraint.append(
            self.abs_wf_semantics(*curr_prog_output_bvs)
        )

        return z3.And(curr_prog_excludes_eg_constraint, context)

    def finite_synthesis_new_negative(self):
        """
        attempt to synthesize a program that works for current positive examples, and
        additionally excludes a negative example that the current synthesized program
        includes on success, return with components in component_library updated with
        their lineno assignments.
        """

        context = z3.Context()
        solver = z3.Solver(ctx=context)
        solver.set("timeout", self.timeout)

        self._reset_linenos()
        self._instantiate_linenos(context=context)
        self._reset_instance_ids()

        lineno_constraints = self.get_all_lineno_constraints(context=context)
        solver.add(lineno_constraints)

        works_for_examples = self.get_works_for_positive_negative_examples_constraint(
            context=context
        )
        solver.add(works_for_examples)

        # create new abstract inputs and abstract outputs that the new prog should
        # exclude, but the old prog should include
        new_neg_conc_out = z3.BitVec(
            "new_neg_conc_out", Component.COMPONENT_BV_BITWIDTH, ctx=context
        )
        new_neg_abs_in_lst = z3.BitVecs(
            "new_neg_abs0_in new_neg_abs1_in new_neg_abs2_in new_neg_abs3_in",
            Component.COMPONENT_BV_BITWIDTH,
            ctx=context,
        )

        # new prog does not contain a particular concrete value
        new_prog_excludes_neg_eg_constraint = (
            self.get_new_prog_excludes_neg_eg_constraint(
                new_neg_conc_out=new_neg_conc_out,
                new_neg_abs_in_lst=new_neg_abs_in_lst,
                context=context,
            )
        )
        solver.add(new_prog_excludes_neg_eg_constraint)

        # old prog contains the concrete value
        curr_prog_includes_neg_eg_constraint = (
            self.get_curr_prog_includes_neg_eg_constraint(
                new_neg_conc_out=new_neg_conc_out,
                new_neg_abs_in_lst=new_neg_abs_in_lst,
                context=context,
            )
        )
        solver.add(curr_prog_includes_neg_eg_constraint)

        smt2_str = solver.to_smt2()
        if self.smt_filename:
            self._write_smt_to_file(smt2_str)

        issat = solver.check()

        stats = solver.statistics()
        try:
            time = stats.get_key_value("time")
            print("solver time (secs): ", time)
        except z3.Z3Exception as e:
            pass

        if str(issat) == "sat":

            # solver returned a model -- we have a candidate program
            synthesis_model = solver.model()

            # save the lineno assignnments in last_synthesized_lineno_assignment: if
            # they correspond to an invalid program after verify(), we will explicitly
            # forbid them; currently, these are saved as a dictionary of *strings* to
            # *ints* e.g.: {'lo7': 4, 'lo8': 7, 'lo9': 9, 'lo5': 6), 'lo4': 8, 'lo6':
            # 5}.
            all_lineno_bvs = set()
            for component in self.component_library:
                if isinstance(component, (VarInputComponent)):
                    continue
                if isinstance(component, (VarOutputComponent)):
                    continue
                for lineno_bv in component.get_lineno_out_bvs():
                    all_lineno_bvs.add(lineno_bv)
                for input_lineno_bv in component.get_lineno_in_bvs():
                    all_lineno_bvs.add(input_lineno_bv)

            for lineno_bv in all_lineno_bvs:
                self.last_synthesized_lineno_assignment[str(lineno_bv)] = (
                    synthesis_model[lineno_bv].as_long()
                )

            # self._print_finite_synthesis_model(model=synthesis_model)
            self._update_lineno_assignments_from_finite_synthesis_model(
                model=synthesis_model
            )
            self._update_synthesized_program_string()

            negative_example_abs_inputs = [
                synthesis_model[bv].as_long() for bv in new_neg_abs_in_lst
            ]
            negative_example_conc_output = synthesis_model[new_neg_conc_out].as_long()
            new_negative_example = tuple(
                negative_example_abs_inputs + [negative_example_conc_output]
            )

            del context
            del solver
            z3.Z3_reset_memory()

            return new_negative_example

        elif str(issat) == "unknown":

            # solver returned unknown, cannot proceed
            reason_unknown = str(solver.reason_unknown())

            del context
            del solver
            z3.Z3_reset_memory()

            raise RuntimeError(f"synthesis failed: {reason_unknown}")

        elif str(issat) == "unsat":

            del context
            del solver
            z3.Z3_reset_memory()

            # solver returned unsat, we cannot proceed
            return False

    def construct_prog(self, instance_id, context):
        """
        construct a program using the lineno assignments from finite synthesis
        """

        prog_conn = []
        philib = self.get_philib(instance_id, context=context)
        prog_conn.append(philib)

        # first sort the component library by output lineno assignments
        # -- the component with the smallest lineno assignment should come
        # first in our program
        component_library_sorted = sorted(
            self.component_library, key=lambda x: x.output_lineno_assignments[0]
        )

        for component in component_library_sorted:
            if isinstance(component, (VarInputComponent)):
                continue
            for component_input_param, component_input_lineno_assignment in zip(
                component.get_param_in_bvs(instance_id),
                component.input_lineno_assignments,
            ):

                pulls_from_component = component_library_sorted[
                    component_input_lineno_assignment
                ]
                pulls_from_component_output = pulls_from_component.get_param_out_bvs(
                    instance_id
                )
                pulls_from_component_output_bv = pulls_from_component_output[-1]
                prog_conn.append(
                    component_input_param == pulls_from_component_output_bv
                )

        prog_conn = z3.And(prog_conn, context)

        return prog_conn

    def verify(self):
        """
        verify if the current synthesized program works for all inputs
        """

        context = z3.Context()
        solver = z3.Solver(ctx=context)
        solver.set("timeout", self.timeout)

        self._reset_linenos()
        self._instantiate_linenos(context=context)
        self._reset_instance_ids()
        self._instantiate_new_input_output_params(context=context)

        prog_conn = self.construct_prog(instance_id=-1, context=context)
        solver.add(prog_conn)

        abs_in0_value, abs_in0_mask, abs_in1_value, abs_in1_mask = abs_in_lst = (
            self._get_prog_input_bvs(instance_id=-1)
        )
        abs_out0_value, abs_out0_mask = self._get_prog_output_bvs(instance_id=-1)
        conc_in0, conc_in1, conc_out0 = z3.BitVecs(
            "conc_in0 conc_in1 conc_out0",
            Component.COMPONENT_BV_BITWIDTH,
            ctx=context,
        )

        prog_spec_not = []
        prog_spec_not.append(
            self.abs_contains_semantics(conc_in0, abs_in0_value, abs_in0_mask)
        )
        prog_spec_not.append(
            self.abs_contains_semantics(conc_in1, abs_in1_value, abs_in1_mask)
        )
        prog_spec_not.append(self.conc_func_semantics(conc_in0, conc_in1, conc_out0))
        prog_spec_not.append(
            z3.Not(
                self.abs_contains_semantics(conc_out0, abs_out0_value, abs_out0_mask),
                ctx=context,
            )
        )

        prog_spec_not = z3.And(prog_spec_not, context)
        solver.add(prog_spec_not)

        issat = solver.check()

        stats = solver.statistics()
        try:
            time = stats.get_key_value("time")
            print("solver time (secs): ", time)
        except z3.Z3Exception as e:
            pass

        if str(issat) == "sat":
            synthesis_model = solver.model()

            # this program is invalid, save the combination of line numbers to
            # unsound_lineno_assignments list
            self.unsound_lineno_assignments.append(
                frozenset(self.last_synthesized_lineno_assignment.items())
            )

            # these lineno assignments didn't work, we can clear them because we
            # have saved them in unsound_lineno_assignments.
            self.last_synthesized_lineno_assignment.clear()

            # collect positive counterexample that didn't work
            positive_example_abs_inputs = [
                synthesis_model[bv].as_long() for bv in abs_in_lst
            ]
            positive_example_conc_output = synthesis_model[conc_out0].as_long()
            new_positive_example = tuple(
                positive_example_abs_inputs + [positive_example_conc_output]
            )

            self.unsound_operators.add(self.curr_synthesized_program_str_lambda)

            del context
            del solver
            z3.Z3_reset_memory()

            return new_positive_example

        elif str(issat) == "unknown":

            # solver returned unknown, cannot proceed
            reason_unknown = str(solver.reason_unknown())

            del context
            del solver
            z3.Z3_reset_memory()

            raise RuntimeError(f"verification failed: {reason_unknown}")

        elif str(issat) == "unsat":
            self.sound_operators.add(self.curr_synthesized_program_str_lambda)

            del context
            del solver
            z3.Z3_reset_memory()

            return False

    def valid_negative_example(self, negative_example):
        """
        for negative example (P, Q, z), check if exists x in P, y in Q: f(x, y) == z if
        yes (sat), this means P, Q, z is a positive example instead. if no (unsat), this
        is indeed a negative example.
        """

        context = z3.Context()
        solver = z3.Solver(ctx=context)
        solver.set("timeout", self.timeout)

        conc_in0, conc_in1, conc_out0 = z3.BitVecs(
            "conc_in0 conc_in1 conc_out0",
            Component.COMPONENT_BV_BITWIDTH,
            ctx=context,
        )
        abs_in_lst = abs_in0, abs_in1, abs_in2, abs_in3 = z3.BitVecs(
            "abs_in0 abs_in1 abs_in2 abs_in3",
            Component.COMPONENT_BV_BITWIDTH,
            ctx=context,
        )

        check_neg_formula = []

        negative_example_abs_inputs, negative_example_conc_output = (
            negative_example[0 : self.num_inputs],
            negative_example[self.num_inputs],
        )
        for i in zip(negative_example_abs_inputs, abs_in_lst):
            check_neg_formula.append(i[0] == i[1])
        check_neg_formula.append(conc_out0 == negative_example_conc_output)
        check_neg_formula.append(
            self.abs_contains_semantics(conc_in0, abs_in0, abs_in1)
        )
        check_neg_formula.append(
            self.abs_contains_semantics(conc_in1, abs_in2, abs_in3)
        )
        check_neg_formula.append(
            self.conc_func_semantics(conc_in0, conc_in1, conc_out0)
        )

        solver.append(z3.And(check_neg_formula, context))

        issat = solver.check()

        stats = solver.statistics()
        try:
            time = stats.get_key_value("time")
            print("solver time (secs): ", time)
        except z3.Z3Exception as e:
            pass

        if str(issat) == "sat":
            model = solver.model()
            print(f"inputs: {model[conc_in0]}, {model[conc_in1]}")

            del context
            del solver
            z3.Z3_reset_memory()

            return False

        elif str(issat) == "unsat":

            del context
            del solver
            z3.Z3_reset_memory()

            return True

    def run_cegis(self):
        """
        step A: use CEGIS to find a *sound* candidate.
        step B: use CEGIS to refine the candidate for improved precision.
        """

        state = CegisState.INIT_POS

        print()
        print(f"initializing examples ...")
        state = CegisState.INIT_POS
        self.get_initial_positive_examples()
        print(f"done")
        print(f"current positive examples: {len(self.positive_examples)}")
        print(self.positive_examples)
        print(f"current negative examples: {len(self.negative_examples)}")
        print(self.negative_examples)

        if self.stop_after_iter == -1:
            return

        if self.do_inject_prog:
            print("prog injected: ")
            print(self.curr_synthesized_program_str)
            print(self.curr_synthesized_program_str_lambda)
            state = CegisState.VERIF_POS_NEG
        else:
            state = CegisState.SYNTH_POS_NEG

        print()
        self.cegis_iter = 0

        print("***********************************")
        print("searching for a sound candidate ...")
        print("***********************************")

        while True:
            print(state)
            if state == CegisState.SYNTH_POS_NEG:
                print(f"iteration {self.cegis_iter} ...")
                print(f"current positive examples: {len(self.positive_examples)}")
                print(self.positive_examples)
                print(f"current negative examples: {len(self.negative_examples)}")
                print(self.negative_examples)

                self.finite_synthesis_positive_negative()
                print("finite_synthesis_positive_negative success")
                print("\nsynthezied program:")
                print(self.curr_synthesized_program_str)
                print("synthezied program lambda:")
                print(self.curr_synthesized_program_str_lambda)
                print()
                state = CegisState.VERIF_POS_NEG

            elif state == CegisState.VERIF_POS_NEG:
                print("verifying synthesized program")
                new_positive_counterexample = self.verify()
                if new_positive_counterexample:
                    # we got a positive counterexample, add it to our set, and try
                    # synthesis again
                    print("we got a positive counterexample:")
                    print(new_positive_counterexample)
                    self.positive_examples.add(new_positive_counterexample)
                    state = CegisState.SYNTH_POS_NEG
                    self.cegis_iter += 1
                    print("-------------------")
                else:
                    print("sound. no counterexample")
                    break

        if self.stop_after_iter == -2:
            return

        print()
        print("******************************************")
        print("sound candidate found")
        print("searching for a more precise candidate ...")
        print("******************************************")
        print()

        state = CegisState.SYNTH_NEW_NEG
        self.cegis_iter = 0

        while True:
            print(state)
            if state == CegisState.SYNTH_NEW_NEG:
                print(f"iteration {self.cegis_iter} ...")
                print(f"current positive examples: {len(self.positive_examples)}")
                print(self.positive_examples)
                print(f"current negative examples: {len(self.negative_examples)}")
                print(self.negative_examples)

                new_negative_counterexample = self.finite_synthesis_new_negative()
                if new_negative_counterexample:
                    print(f"new negative counterexample:")
                    print(new_negative_counterexample)
                    self.last_negative_counterexample = new_negative_counterexample
                    # self.negative_examples.add(new_negative_counterexample)
                    print("\nsynthezied program:")
                    print(self.curr_synthesized_program_str)
                    print("synthezied program lambda:")
                    print(self.curr_synthesized_program_str_lambda)
                    print()
                    state = CegisState.VERIF_NEW_NEG
                else:
                    print("no negative example, break with success")
                    break

            elif state == CegisState.VERIF_NEW_NEG:
                print("verifying synthesized new negative program")
                new_positive_counterexample = self.verify()
                if new_positive_counterexample:
                    print("unsound")
                    print("we got a positive counterexample:")
                    print(new_positive_counterexample)
                    self.positive_examples.add(new_positive_counterexample)
                    print("deleting negative example that led to unsoundness")
                    del self.last_negative_counterexample
                    print("restoring old program (lineno assignments) ...")
                    self._restore_old_lineno_assignments()
                    print()
                    print(self.curr_synthesized_program_str)
                    print("try synthesis again")
                    state = CegisState.SYNTH_NEW_NEG
                    self.cegis_iter += 1
                    print("-------------------")
                else:
                    self.negative_examples.add(self.last_negative_counterexample)
                    print("we did not get a counterexample, try negative synthesis")
                    state = CegisState.SYNTH_NEW_NEG
                    self.cegis_iter += 1
                    print("-------------------")

            if self.cegis_iter > self.stop_after_iter:
                print(f"stopped after iteration {self.stop_after_iter}.")
                return

        # reached here means synthesis succeeded.

        print()
        print("*********************************")
        print("sound and precise candidate found")
        print("*********************************")

        print()
        print("final synthezied program:")
        print(self.curr_synthesized_program_str)
        print("final synthezied program lambda:")
        print(self.curr_synthesized_program_str_lambda)

        return


def main(args):
    components_ = [
        (ConstComponent, 0),
        (ConstComponent, 1),
        (ConstComponent, Component.COMPONENT_BV_BITWIDTH - 1),
        (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
        NotComponent,
        AddComponent,
        SubComponent,
        AndComponent,
        OrComponent,
        XorComponent,
        LogicalRightShiftComponent,
        ArithmeticLeftShiftComponent,
        ArithmeticRightShiftComponent,
        # UnsignedGreaterOrEqualComponent,
        # SignedGreaterOrEqualComponent,
        # UnsignedGreaterThanComponent,
        # SignedGreaterThanComponent,
        # SelectComponent,
    ]

    # set the components' bitwidth
    Component.COMPONENT_BV_BITWIDTH = args.bw

    # get the spec function from our library of specifications
    abs_prog_spec = abs_prog_spec_mappings[args.spec]

    # set the z3 related parameters
    if args.z3_tactic_smt:
        z3.set_param("tactic.default_tactic", "smt")
        z3.set_param("sat.smt", "true")

    if args.z3_verbose:
        z3.set_param("verbose", 1)

    if args.z3_parallel:
        z3.set_param("parallel.enable", "true")

    if args.seed:
        init_seed(args.seed)
    else:
        init_seed(9001)

    components_ = []
    (
        conc_func_semantics,
        abs_wf_semantics,
        abs_contains_semantics,
        eg_generator_func,
        input_arity,
        output_arity,
    ) = abs_prog_spec(components_, args.cisc)

    synthesizer = Cegis(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=abs_wf_semantics,
        abs_contains_semantics=abs_contains_semantics,
        eg_generator_func=eg_generator_func,
        num_inputs=input_arity,
        num_outputs=output_arity,
        components=components_,
        num_initial_inputs=args.numinitinputs,
        log_to_file=args.logf,
        log_to_console=args.logc,
        stop_after_iter=args.stopiter,
        enable_invalid_linenos_opt=args.opt_invalid_linenos,
        enable_invalid_conns_opt=args.opt_invalid_conns,
        timeout=args.timeout * 1000,
        smt_filename=args.smt_filename,
        prog_to_inject=args.inject,
    )

    synthesizer.run_cegis()
    soundops, unsoundops = synthesizer.sound_operators, synthesizer.unsound_operators

    if args.print_ops:
        print()
        print("---------------")
        print("# sound ops:", len(soundops))
        for op in soundops:
            print(op)
        print("---------------")
        print("# unsound ops:", len(unsoundops))
        for op in unsoundops:
            print(op)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--num-init-inputs",
        dest="numinitinputs",
        type=int,
        help="no. of initial input examples to try for finite synthesis",
        default=4,
    )
    parser.add_argument(
        "--logf",
        help="log to file",
        action=argparse.BooleanOptionalAction,
        default=False,
    )
    parser.add_argument(
        "--logc",
        help="log to console",
        action=argparse.BooleanOptionalAction,
        default=False,
    )
    parser.add_argument(
        "--stop-iter",
        dest="stopiter",
        type=int,
        default=10000000,
        help="stop after iteration #. "
        "special cases: -1: stop after initializing examples; -2: stop after first CEGIS loop",
    )

    parser.add_argument(
        "--opt-invalid-linenos",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="use optimization that forbids invalid lineno assignments (ones that led "
        "to counterexamples) in future iterations of cegis",
    )
    parser.add_argument(
        "--opt-invalid-conns",
        action=argparse.BooleanOptionalAction,
        help="use optimization that elides superflous clauses from psiconn",
        default=False,
    )
    parser.add_argument(
        "--timeout",
        type=int,
        help="solver timeout in seconds (default is 4294967295)",
        default=4294967295,
    )
    parser.add_argument(
        "--smt-filename",
        type=str,
        dest="smt_filename",
        help="save the smtlib query to this file, before every invocation of the Z3 solver",
    )
    parser.add_argument("--bw", type=int, help="component bitwidth", default=8)
    parser.add_argument(
        "--spec",
        choices=abs_prog_spec_mappings.keys(),
        help="which abstract operator do we want to synthesize? (default: tnum_add)",
        default="tnum_add",
    )
    parser.add_argument(
        "--inject",
        required=False,
        choices=inject_prog_mappings.keys(),
        help="inject a known implementation of the program into the cegis loop",
    )
    parser.add_argument(
        "--seed",
        required=False,
        type=int,
        help="random seed for initializing inputs",
    )
    parser.add_argument(
        "--cisc",
        required=False,
        help="use cisc components?",
        action=argparse.BooleanOptionalAction,
        default=False,
    )
    parser.add_argument(
        "--print-ops",
        required=False,
        help="print all sound and unsound operators discovered",
        action=argparse.BooleanOptionalAction,
        dest="print_ops",
        default=False,
    )
    parser.add_argument(
        "--z3-tactic-smt", action=argparse.BooleanOptionalAction, default=False
    )
    parser.add_argument(
        "--z3-verbose", action=argparse.BooleanOptionalAction, default=False
    )
    parser.add_argument(
        "--z3-parallel", action=argparse.BooleanOptionalAction, default=False
    )
    args = parser.parse_args()
    main(args)
