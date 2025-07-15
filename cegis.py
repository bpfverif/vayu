from dataclasses import dataclass, field
from typing import Callable
from component import *
import logging
import itertools
from spec import get_prog_spec
import math
from datetime import datetime
import argparse
import sys
import parse_to_lambda


class Cegis:

    def __init__(
        self,
        prog_spec,
        num_inputs,
        num_outputs,
        components,
        num_initial_inputs,
        log_to_file,
        log_to_console,
        stop_after_iter,
        use_model_completion,
    ):

        self.prog_spec_lambda = prog_spec
        self.num_inputs = num_inputs
        self.num_outputs = num_outputs
        self.stop_after_iter = stop_after_iter
        self.use_model_completion = use_model_completion
        self.num_initial_inputs = num_initial_inputs
        self._init_logging(log_to_file, log_to_console)
        self._init_component_library(components=components)
        self._init_invalid_connections()
        self.last_synthesized_lineno_assignment = {}
        self.invalid_lineno_assignments = []

    def _reset_instance_ids(self):
        for component in self.component_library:
            component.reset_instance_id()

    def _instantiate_new_input_output_params(self):
        for component in self.component_library:
            component.instantiate_new_input_output_params()

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

    def _init_component_library(self, components):
        """
        initialize component_library by instantiating components given to us
        in 'components'.
        also create new lineno bitvectors for each component
        """

        # add input and output components to the given base library of components,
        # based on the to-be-synthesized program's arity
        for _ in range(0, self.num_inputs):
            components.insert(0, VarInputComponent)
        for _ in range(0, self.num_outputs):
            components.append(VarOutputComponent)

        # each component (including input and outputs) occur on a new line.
        # decide what is the bitwidth of the maximum line number
        Component.LINENO_BV_BITWIDTH = 2 ** math.ceil(math.log2(len(components)))

        # initialize the components, and save the instances in
        # self.component_library
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

        self.logger.debug(pprint.pformat(self.component_library))

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

        prog_input_lineno_output_bvs = set()
        prog_output_lineno_output_bvs = set()
        for component in self.component_library:
            if isinstance(component, VarInputComponent):
                for output_lineno_bv in component.get_lineno_out_bvs():
                    prog_input_lineno_output_bvs.add(output_lineno_bv)
            if isinstance(component, VarOutputComponent):
                for output_lineno_bv in component.get_lineno_out_bvs():
                    prog_output_lineno_output_bvs.add(output_lineno_bv)

        # skip assigning program inputs directly to program outputs
        # e.g. if program input is O0 (lo0), and program output is O7 (lo7)
        # skip asserting that (lo0 == lo7 ==> O0 == O7)
        prog_input_to_prog_output = list(
            itertools.product(
                prog_input_lineno_output_bvs, prog_output_lineno_output_bvs
            )
        )
        self.invalid_connections.extend(prog_input_to_prog_output)

        # skip assigning one program input to other program input
        # e.g. if program inputs are O0 (lo0), and O1 (lo1)
        # skip asserting that (lo0 == lo1 ==> O0 == O1)
        prog_input_to_prog_input = list(
            itertools.combinations(prog_input_lineno_output_bvs, 2)
        )
        self.invalid_connections.extend(prog_input_to_prog_input)

        # skip assigning one program output to other program output
        # e.g. if program outputs are O7 (lo7), and O8 (lo8)
        # skip asserting that (lo7 == lo8 ==> O7 == O88)
        prog_output_to_prog_output = list(
            itertools.combinations(prog_output_lineno_output_bvs, 2)
        )
        self.invalid_connections.extend(prog_output_to_prog_output)

        # skip assigning a component's input param location to
        # the same component's other input param location
        # e.g. consider component O5 (lo5) := I50 (li50) ^ I51 (li51)
        # skip asserting that (li50 == li51 ==> i50 == I51)
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

        # skip assigning a component's output location to its input param locations
        # e.g. consider component O5 (lo5) := I50 (li50) ^ I51 (li51)
        # skip the following assertions:
        # (lo5 == li50 ==> O5 == I50)
        # (lo5 == li51 ==> O5 == I51)
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

    def get_initial_concrete_example_input_outputs(self):
        """
        initialize the starting set of concrete example inputs
        'concrete_example_input_outputs'. we use a solver to do this,
        by using the spec given to us, rather than manually creating the examples.
        also initialize line number bitvectors self.prog_input_linenos and
        self.prog_output_linenos
        """

        self._reset_instance_ids()
        self._instantiate_new_input_output_params()

        prog_input_bvs = self._get_prog_input_bvs(-1)
        prog_output_bvs = self._get_prog_output_bvs(-1)

        iosolver = z3.Solver()
        prog_spec = self.prog_spec_lambda(prog_input_bvs, prog_output_bvs)
        iosolver.append(prog_spec)

        self.concrete_example_input_outputs = {}
        while len(self.concrete_example_input_outputs) < self.num_initial_inputs:

            issat = iosolver.check()
            if not str(issat) == "sat":
                raise RuntimeError("unable to generate initial i/o assignements")
            io_model = iosolver.model()

            if self.use_model_completion:
                input_i = tuple(
                    [
                        io_model.eval(prog_input_bv_i, model_completion=True).as_long()
                        for prog_input_bv_i in prog_input_bvs
                    ]
                )
                output_i = tuple(
                    [
                        io_model.eval(prog_output_bv_i, model_completion=True).as_long()
                        for prog_output_bv_i in prog_output_bvs
                    ]
                )
            else:
                input_i = tuple(
                    [
                        io_model[prog_input_bv_i].as_long()
                        for prog_input_bv_i in prog_input_bvs
                    ]
                )
                output_i = tuple(
                    [
                        io_model[prog_output_bv_i].as_long()
                        for prog_output_bv_i in prog_output_bvs
                    ]
                )

            self.concrete_example_input_outputs[input_i] = output_i
            curr_inputs = []
            for input in self.concrete_example_input_outputs:
                for inputi, bvi in zip(prog_input_bvs, input):
                    curr_inputs.append(bvi != inputi)
            curr_inputs = z3.And(curr_inputs)
            iosolver.add(curr_inputs)

        self.concrete_example_inputs = set(self.concrete_example_input_outputs.keys())

    def get_psicons(self):
        """
        assert that the output line number bitvectors of each component
        in our component library are different -- each component should
        appear on a different line.
        e.g. lo1 != lo2 AND lo2 != lo3, and so on
        """
        all_output_lineno_bvs = set()
        for component in self.component_library:
            for output_lineno_bv in component.get_lineno_out_bvs():
                all_output_lineno_bvs.add(output_lineno_bv)
        psicons = z3.Distinct(all_output_lineno_bvs)
        return z3.And(psicons)

    def get_psiacyc(self):
        """
        for every component, if x is input (with location lx), y is output
        (location ly, where ly is the component's final position) then
        lx should be earlier than ly
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
        return z3.And(psiacyc)

    def get_psibounds(self):
        """
        for all the "semantic" components, all input line numbers li are:
        0 <= li <= num_inputs + num_components - 1 all output line numbers
        lo are: num_inputs < lo < self.num_inputs + num_components -1
        """

        all_lineno_input_bvs = set()
        all_lineno_output_bvs = set()
        for component in self.component_library:
            if isinstance(component, VarInputComponent | VarOutputComponent):
                continue
            # TODO assert that VarOutputComponent's line numbers are ==
            # the prog_length?
            for output_lineno_bv in component.get_lineno_out_bvs():
                all_lineno_output_bvs.add(output_lineno_bv)
            for input_lineno_bv in component.get_lineno_in_bvs():
                all_lineno_input_bvs.add(input_lineno_bv)

        prog_length = len(self.component_library) - self.num_outputs
        zero_lineno = z3.BitVecVal(0, Component.LINENO_BV_BITWIDTH)
        max_lineno = z3.BitVecVal(prog_length - 1, Component.LINENO_BV_BITWIDTH)

        psibounds_input = []
        psibounds_output = []
        for lineno_bv in all_lineno_input_bvs:
            psibounds_input.append(z3.ULE(zero_lineno, lineno_bv))
            psibounds_input.append(z3.ULE(lineno_bv, max_lineno))
        for lineno_bv in all_lineno_output_bvs:
            psibounds_output.append(z3.ULE(self.num_inputs, lineno_bv))
            psibounds_output.append(z3.ULE(lineno_bv, max_lineno))

        psibounds = psibounds_input + psibounds_output
        return z3.And(psibounds)

    def get_psiwfp(self):
        """
        psiwfp = psicons AND psiacyc AND psibounds
        """
        psicons = self.get_psicons()
        self.logger.debug("psicons")
        self.logger.debug(psicons)

        psiacyc = self.get_psiacyc()
        self.logger.debug("psiacyc")
        self.logger.debug(psiacyc)

        psibounds = self.get_psibounds()
        self.logger.debug("psibounds")
        self.logger.debug(psibounds)

        psiwfp = z3.And(psibounds, psicons, psiacyc)

        return psiwfp

    def get_invalid_lineno_assignments(self):
        """
        get a formula that corresponds to all the invalid programs, that we have saved
        in invalid_lineno_assignments. For e.g. let's say invalid_lineno_assignments =
        [{lo1:3, lo2: 2, lo1: 1}, {lo1:2, lo2: 3, lo1: 1}] Then the formula is: (lo1 !=
        3 OR lo2 != 2 OR lo1 != 1) AND (lo1 != 2 OR lo2 != 3 OR lo1 != 1). This formula
        explicitly forbids the particular combination of line numbers that correspond to
        each invalid program we have discovered and saved.
        """

        invalid = []
        for invalid_lineno_assignment in self.invalid_lineno_assignments:
            invalid_i = [
                output_lineno_bv == invalid_lineno
                for output_lineno_bv, invalid_lineno in invalid_lineno_assignment
            ]
            invalid.append(z3.Not(z3.And(invalid_i)))
        return z3.And(invalid)

    def get_psiconn(self, instance_id):
        """
        connect the line number bitvectors, with the corresponding
        component bitvectors, e.g.
        Implies(lo1 == li11, O1 == I11) AND Implies(lo1 == li11, O1 == I11)
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
            psiconn.append(z3.Implies(lineno0 == lineno1, param0 == param1))

        self.logger.debug("psiconn")
        self.logger.debug(pprint.pformat(psiconn))
        return z3.And(psiconn)

    def get_philib(self, instance_id):
        """
        get a formula representing all the components in our library.
        e.g. ff our component library contains AndComponent, and OrComponent,
        this returns And(O1 == I11 & I12, O2 == I21 | I22)
        """
        philib = []
        for component in self.component_library:
            if isinstance(component, VarInputComponent):
                continue
            philib.append(component.make_expr(instance_id))

        self.logger.debug("philib")
        self.logger.debug(pprint.pformat(philib))
        philib = z3.And(philib)
        return philib

    def _update_synthesized_program_string(self):

        # first sort the component library by output lineno assignments
        # -- the component with the smallest lineno assignment should come
        # first in our program string
        component_library_sorted = sorted(
            self.component_library, key=lambda x: x.output_lineno_assignments[0]
        )
        self.logger.debug(
            "_update_synthesized_program_string: component_library_sorted"
        )
        self.logger.debug(pprint.pformat(component_library_sorted))

        program_str = ""
        for component in component_library_sorted:
            program_str += (component.get_expr_str()) + "\n"

        self.curr_synthesized_program_str = program_str
        self.curr_synthesized_program_str_lambda = parse_to_lambda.construct_lambda(
            self.curr_synthesized_program_str, self.num_inputs, self.num_outputs
        )
        self.logger.debug("current synthesized program string")
        self.logger.debug(self.curr_synthesized_program_str)

    def _print_finite_synthesis_model(self, model):
        self.logger.debug("full finite synthesis model:")
        self.logger.debug(model)
        self.logger.debug("finite synthesis model (only input and output linenos):")
        for component in self.component_library:
            for lineno_in_bv in component.get_lineno_in_bvs():
                self.logger.debug(str(lineno_in_bv) + ":" + str(model[lineno_in_bv]))
            for lineno_out_bv in component.get_lineno_out_bvs():
                self.logger.debug(str(lineno_out_bv) + ":" + str(model[lineno_out_bv]))

    def _update_lineno_assignments_from_finite_synthesis_model(self, model):
        for component in self.component_library:
            component.update_lineno_assignments(model)

    def finite_synthesis(self):
        """
        attempt to synthesize a program that works for current input examples.
        on success, return with components in component_library updated with
        their lineno assignments.
        """
        finite_synthesis_formula = []

        input_lineno_constraints = []
        # first input occurs on line 0, second one line 1, etc.
        # lo00 == 0, lo01 == 1, and so on
        for i, prog_input_i in enumerate(self.prog_inputs):
            for lineno_bv in prog_input_i.get_lineno_out_bvs():
                input_lineno_constraints.append(lineno_bv == i)

        finite_synthesis_formula.append(z3.And(input_lineno_constraints))
        self.logger.debug("input_lineno_constraints:")
        self.logger.debug(input_lineno_constraints)

        # first output occurs on line prog_length, second on prog_length + 1, etc.
        # lox0 == N, loy0 = N + 1, and so on
        prog_length = len(self.component_library) - self.num_outputs
        output_lineno_constraints = []
        for i, prog_output_i in enumerate(self.prog_outputs, start=prog_length):
            for lineno_bv in prog_output_i.get_lineno_out_bvs():
                output_lineno_constraints.append(lineno_bv == i)

        finite_synthesis_formula.append(z3.And(output_lineno_constraints))
        self.logger.debug("output_lineno_constraints:")
        self.logger.debug(output_lineno_constraints)

        invalid_assignments = self.get_invalid_lineno_assignments()
        finite_synthesis_formula.append(invalid_assignments)

        psiwfp = self.get_psiwfp()
        finite_synthesis_formula.append(psiwfp)

        self._reset_instance_ids()

        self.logger.debug("***********")
        for concrete_input_instance_idx, concrete_input_value in enumerate(
            self.concrete_example_input_outputs
        ):
            self.logger.debug("input:")
            self.logger.debug(concrete_input_value)

            # instantiate new program input/output parameters to be used
            # for this run of the synthesis
            self._instantiate_new_input_output_params()

            works_for_inputs = []
            for i in range(0, self.num_inputs):
                concrete_input_i = concrete_input_value[i]
                prog_input_i = self.prog_inputs[i]
                prog_input_param_i = prog_input_i.get_param_out_bvs(instance_id=-1)[-1]
                works_for_inputs.append(prog_input_param_i == concrete_input_i)

            works_for_inputs = z3.And(works_for_inputs)

            self.logger.debug("works_for_inputs:")
            self.logger.debug(works_for_inputs)

            finite_synthesis_formula.append(z3.And(works_for_inputs))

            psiconn = self.get_psiconn(instance_id=-1)
            finite_synthesis_formula.append(psiconn)

            philib = self.get_philib(instance_id=-1)
            finite_synthesis_formula.append(philib)

            prog_input_bvs = self._get_prog_input_bvs(instance_id=-1)
            prog_output_bvs = self._get_prog_output_bvs(instance_id=-1)

            prog_spec = self.prog_spec_lambda(prog_input_bvs, prog_output_bvs)

            self.logger.debug("prog_spec")
            self.logger.debug(prog_spec)

            finite_synthesis_formula.append(prog_spec)

            self.logger.debug("-----------")

        self.logger.debug("***********")

        finite_synthesis_formula = z3.And(finite_synthesis_formula)

        self.logger.debug("finite_synthesis_formula:")
        self.logger.debug(finite_synthesis_formula)

        synth = z3.Solver()
        synth.add(finite_synthesis_formula)

        self.logger.debug("***********")
        self.logger.debug("solver:")
        self.logger.debug(synth.sexpr())
        self.logger.debug("***********")

        issat = synth.check()
        self.logger.debug(issat)

        if str(issat) == "sat":

            # solver returned a model -- we have a candidate program
            synthesis_model = synth.model()

            all_output_lineno_bvs = set()
            for component in self.component_library:
                if isinstance(component, (VarInputComponent)):
                    continue
                if isinstance(component, (VarOutputComponent)):
                    continue
                for output_lineno_bv in component.get_lineno_out_bvs():
                    all_output_lineno_bvs.add(output_lineno_bv)

            # save the lineno assignnments; if they correspond to an invalid program
            # after verify(), we will explicitly forbid them
            for output_lineno_bv in all_output_lineno_bvs:
                self.last_synthesized_lineno_assignment[output_lineno_bv] = (
                    synthesis_model[output_lineno_bv].as_long()
                )

            self.logger.debug("last_synthesized_lineno_assignment: ")
            self.logger.debug(self.last_synthesized_lineno_assignment)

            self._print_finite_synthesis_model(model=synthesis_model)
            self._update_lineno_assignments_from_finite_synthesis_model(
                model=synthesis_model
            )
            self._update_synthesized_program_string()

        elif str(issat) == "unknown":

            # solver returned unknown, cannot proceed
            reason_unknown = str(synth.reason_unknown())
            self.logger.debug(reason_unknown)
            raise RuntimeError(f"synthesis failed: {reason_unknown}")

        elif str(issat) == "unsat":

            # solver returned unsat, we cannot proceed
            unsat_core = str(synth.unsat_core())
            self.logger.debug(unsat_core)
            raise RuntimeError(f"synthesis failed: {unsat_core}")

    def construct_prog(self, instance_id):
        """
        construct a program using the lineno assignments from finite synthesis
        """

        prog_conn = []
        philib = self.get_philib(instance_id)
        prog_conn.append(philib)

        # first sort the component library by output lineno assignments
        # -- the component with the smallest lineno assignment should come
        # first in our program
        component_library_sorted = sorted(
            self.component_library, key=lambda x: x.output_lineno_assignments[0]
        )

        self.logger.debug("***********")
        for component in component_library_sorted:
            if isinstance(component, (VarInputComponent)):
                continue
            for component_input_param, component_input_lineno_assignment in zip(
                component.get_param_in_bvs(instance_id),
                component.input_lineno_assignments,
            ):

                self.logger.debug(component.__class__.__name__)
                self.logger.debug(str(component_input_param))
                self.logger.debug(str(component_input_lineno_assignment))

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

                self.logger.debug(str(pulls_from_component.__class__.__name__))
                self.logger.debug(str(pulls_from_component_output_bv))
                self.logger.debug("-----------")

        self.logger.debug("***********")
        prog_conn = z3.And(prog_conn)
        self.logger.debug("prog_conn")
        self.logger.debug(prog_conn)
        return prog_conn

    def verify(self):
        """
        verify if the current synthesized program works for all inputs
        """

        # instantiate new input/output parameters in the component library
        # to be used for this run of the synthesis
        self._reset_instance_ids()
        self._instantiate_new_input_output_params()

        prog_conn = self.construct_prog(instance_id=-1)

        prog_input_bvs = self._get_prog_input_bvs(instance_id=-1)
        prog_output_bvs = self._get_prog_output_bvs(instance_id=-1)
        prog_spec = self.prog_spec_lambda(prog_input_bvs, prog_output_bvs)
        prog_spec_not = z3.Not(prog_spec)

        verification_formula = []
        verification_formula.append(prog_conn)
        verification_formula.append(prog_spec_not)
        verification_formula = z3.And(verification_formula)

        self.logger.debug("verification_formula")
        self.logger.debug(verification_formula)

        verif = z3.Solver()
        verif.add(z3.And(verification_formula))
        self.logger.debug("***********")
        self.logger.debug("solver:")
        self.logger.debug(verif.sexpr())
        self.logger.debug("***********")

        issat = verif.check()
        self.logger.debug(issat)

        if str(issat) == "sat":

            synthesis_model = verif.model()
            concrete_input_output_counterexample = {}

            # this program is invalid, save the combination of line numbers to
            # invalid_lineno_assignments list
            self.invalid_lineno_assignments.append(
                frozenset(self.last_synthesized_lineno_assignment.items())
            )
            self.logger.debug("add to invalid_lineno_assignments:")
            self.logger.debug(self.invalid_lineno_assignments)

            # collect counterexamples that didn't work
            input_does_not_work = tuple(
                [
                    synthesis_model[prog_input_bv].as_long()
                    for prog_input_bv in prog_input_bvs
                ]
            )
            output_does_not_work = tuple(
                [
                    synthesis_model[prog_output_bv].as_long()
                    for prog_output_bv in prog_output_bvs
                ]
            )
            concrete_input_output_counterexample[input_does_not_work] = (
                output_does_not_work
            )
            return concrete_input_output_counterexample

        elif str(issat) == "unknown":

            # solver returned unknown, cannot proceed
            reason_unknown = str(verif.reason_unknown())
            self.logger.debug(reason_unknown)
            raise RuntimeError(f"verification failed: {reason_unknown}")

        elif str(issat) == "unsat":

            # we succeeded in synthesizing a program
            return False

    def run_cegis(self):
        """
        (0) get some initial examples E *from the provided specification S*
        (1) finite synthesis
            (a) synthesize program P (by asking ∃ line numbers) that works for
                examples in E using components provided
        (2) verification
            (a) verify if P satisfies S, ∀ inputs, by asking negated ∃ query
            (b) if a witness is found, add it to E and repeat
            (c) if no witness is found, P satisfies S for all inputs -- we have our program.
        """

        # get initial set of examples
        self.get_initial_concrete_example_input_outputs()

        k = 1
        while True:

            print("-------------------")
            self.logger.debug(f"iteration {k} ...")
            print(f"iteration {k} ...")
            self.logger.debug("current example input set:")
            self.logger.debug(self.concrete_example_input_outputs)
            print("current example input set:")
            print(self.concrete_example_input_outputs)

            # finite synthesis using current set of examples
            self.finite_synthesis()

            self.logger.debug("synthezied program:")
            self.logger.debug(self.curr_synthesized_program_str)
            print("\nsynthezied program:")
            print(self.curr_synthesized_program_str)
            print(self.curr_synthesized_program_str_lambda)

            if k == self.stop_after_iter:
                break

            # verify the current synthesized program
            concrete_input_output_counterexample = self.verify()

            # if we did not get a counterexample, synthesis succeeded
            if not concrete_input_output_counterexample:
                break

            # we got a counterexample, add it to our set
            self.concrete_example_input_outputs |= concrete_input_output_counterexample
            self.concrete_example_inputs = set(
                self.concrete_example_input_outputs.keys()
            )

            print(f"new counterexample:")
            print(concrete_input_output_counterexample)
            self.logger.debug("new counterexample:")
            self.logger.debug(concrete_input_output_counterexample)

            k += 1

        # reached here means synthesis succeeded.
        self.logger.debug("done.")
        self.logger.debug("final synthezied program:")
        self.logger.debug(self.curr_synthesized_program_str)
        print("done.")
        print("\nfinal synthezied program:")
        print(self.curr_synthesized_program_str)
        print(self.curr_synthesized_program_str_lambda)


def main(args):
    # components_ = [
    #     (ConstComponent, 0),
    #     (ConstComponent, 1),
    #     (ConstComponent, 7),
    #     NotComponent,
    #     AddComponent,
    #     SubComponent,
    #     AndComponent,
    #     OrComponent,
    #     XorComponent,
    #     LogicalRightShiftComponent,
    #     ArithmeticLeftShiftComponent,
    #     UnsignedGreaterOrEqualComponent,
    # ]
    components_ = []
    prog_spec, num_inputs, num_outputs = get_prog_spec(components_)
    synthesizer = Cegis(
        prog_spec=prog_spec,
        num_inputs=num_inputs,
        num_outputs=num_outputs,
        components=components_,
        num_initial_inputs=args.numinitinputs,
        log_to_file=args.logf,
        log_to_console=args.logc,
        stop_after_iter=args.stopiter,
        use_model_completion=args.modelcompl,
    )
    synthesizer.run_cegis()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--numinitinputs",
        type=int,
        help="no. of initial input examples to try for finite synthesis",
        default=2,
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
    parser.add_argument("--stopiter", type=int, help="stop after iteration", default=-1)
    parser.add_argument(
        "--modelcompl",
        help="use model completiong",
        action=argparse.BooleanOptionalAction,
        default=False,
    )
    args = parser.parse_args()
    main(args)
