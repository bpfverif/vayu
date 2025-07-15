from dataclasses import dataclass
import z3
from component import *
import pprint


class ProgramBuilder:
    def __init__(self):
        self.idx = 0
        self.components = []
        self.var_inputs = []
        self.var_outputs = []

    def next_id(self):
        idx = self.idx
        self.idx += 1
        return idx

    def varinput_(self):
        component = VarInputComponent()
        component.output_lineno_assignments = [self.next_id()]
        self.var_inputs.append(component)
        self.components.append(component)
        return component

    def varoutput_(self, input_component):
        component = VarOutputComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [self.components.index(input_component)]
        self.var_outputs.append(component)
        self.components.append(component)
        return component

    def const_(self, const_value):
        component = ConstComponent(const_value=const_value)
        component.output_lineno_assignments = [self.next_id()]
        self.components.append(component)
        return component

    def not_(self, in1):
        component = NotComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [self.components.index(in1)]
        self.components.append(component)
        return component

    def neg_(self, in1):
        component = NegComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [self.components.index(in1)]
        self.components.append(component)
        return component

    def add_(self, in1, in2):
        component = AddComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def addof1_(self, in1, in2):
        component = AddComponentCISC1()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def addnoof1_(self, in1, in2):
        component = AddComponentCISC2()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def sub_(self, in1, in2):
        component = SubComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def mul_(self, in1, in2):
        component = MulComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def and_(self, in1, in2):
        component = AndComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def andwnot_(self, in1, in2):
        component = AndComponentCISC2()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def and3_(self, in1, in2, in3):
        component = AndComponentCISC3()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
        ]
        self.components.append(component)
        return component

    def or_(self, in1, in2):
        component = OrComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def or3_(self, in1, in2, in3):
        component = OrComponentCISC3()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
        ]
        self.components.append(component)
        return component

    def xor_(self, in1, in2):
        component = XorComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def ugt_(self, in1, in2):
        component = UnsignedGreaterThanComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def uge_(self, in1, in2):
        component = UnsignedGreaterOrEqualComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def ult_(self, in1, in2):
        component = UnsignedLessThanComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def ule_(self, in1, in2):
        component = UnsignedLessOrEqualComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
        ]
        self.components.append(component)
        return component

    def select_(self, in1, in2, in3):
        component = SelectComponent()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
        ]
        self.components.append(component)
        return component

    def selectwadd_(self, in1, in2, in3, in4):
        component = SelectComponentCISC2()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
            self.components.index(in4),
        ]
        self.components.append(component)
        return component

    def selectcisc3_(self, in1, in2, in3, in4, in5):
        component = SelectComponentCISC3()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
            self.components.index(in4),
            self.components.index(in5),
        ]
        self.components.append(component)
        return component

    def selectcisc4_(self, in1, in2, in3, in4, in5):
        component = SelectComponentCISC4()
        component.output_lineno_assignments = [self.next_id()]
        component.input_lineno_assignments = [
            self.components.index(in1),
            self.components.index(in2),
            self.components.index(in3),
            self.components.index(in4),
            self.components.index(in5),
        ]
        self.components.append(component)
        return component

    def finish(self):
        return Program(self.components, self.var_inputs, self.var_outputs)


@dataclass
class Program:
    components: list
    var_inputs: list
    var_outputs: list

    def set_instance_id(self, id):
        for component in self.components:
            component.instance_id = id

    def semantics(self, context):
        for component in self.components:
            component.instantiate_new_input_output_params(context)

        prog_conn = []

        components_sorted = sorted(
            self.components, key=lambda x: x.output_lineno_assignments[0]
        )

        for component in components_sorted:
            if isinstance(component, VarInputComponent):
                continue
            prog_conn.append(component.make_expr(-1))

            # Connect inputs to outputs of previous components
            for input_param, input_lineno in zip(
                component.input_params[0], component.input_lineno_assignments
            ):
                source_component = components_sorted[input_lineno]
                source_output = source_component.output_params[0][0]
                prog_conn.append(input_param == source_output)

        return z3.And(prog_conn)


def uint_add_1():
    """
    uinterval add with risc components, canonical
    """
    builder = ProgramBuilder()
    al = builder.varinput_()
    au = builder.varinput_()
    bl = builder.varinput_()
    bu = builder.varinput_()
    o6 = builder.const_(0)
    o7 = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    o1 = builder.add_(al, bl)
    o2 = builder.add_(au, bu)
    o3 = builder.ugt_(al, o1)
    o4 = builder.ugt_(au, o2)
    o5 = builder.or_(o3, o4)
    o8 = builder.select_(o5, o6, o1)
    o9 = builder.select_(o5, o7, o2)
    o10 = builder.varoutput_(o8)
    o11 = builder.varoutput_(o9)

    program = builder.finish()
    return program


def uint_add_2():
    """
    uinterval add with cisc components, canonical
    """
    builder = ProgramBuilder()
    al = builder.varinput_()
    au = builder.varinput_()
    bl = builder.varinput_()
    bu = builder.varinput_()
    const0 = builder.const_(0)
    constMAX = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    lyes_overflow = builder.addof1_(al, bl)
    uyes_overflow = builder.addof1_(au, bu)
    lyes_or_uyes_overflow = builder.or_(lyes_overflow, uyes_overflow)
    o3 = builder.selectwadd_(al, bl, const0, lyes_or_uyes_overflow)
    o4 = builder.selectwadd_(au, bu, constMAX, lyes_or_uyes_overflow)
    o10 = builder.varoutput_(o3)
    o11 = builder.varoutput_(o4)

    program = builder.finish()
    return program


def uint_add_3():
    """
    uinterval add with risc components, more precise
    """
    builder = ProgramBuilder()
    al = builder.varinput_()
    au = builder.varinput_()
    bl = builder.varinput_()
    bu = builder.varinput_()
    const0 = builder.const_(0)
    constMAX = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    albl = builder.add_(al, bl)
    aubu = builder.add_(au, bu)
    lno_overflow = builder.ule_(al, albl)
    uyes_overflow = builder.ugt_(au, aubu)
    lno_and_uyes_overflow = builder.and_(lno_overflow, uyes_overflow)
    ofalbl = builder.select_(lno_and_uyes_overflow, const0, albl)
    ofaubu = builder.select_(lno_and_uyes_overflow, constMAX, aubu)
    o10 = builder.varoutput_(ofalbl)
    o11 = builder.varoutput_(ofaubu)

    program = builder.finish()
    return program


def uint_add_4():
    """
    uinterval add with cisc+ components, more precise
    """
    builder = ProgramBuilder()
    al = builder.varinput_()
    au = builder.varinput_()
    bl = builder.varinput_()
    bu = builder.varinput_()
    const0 = builder.const_(0)
    const255 = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    noofalbl = builder.addnoof1_(al, bl)
    ofaubu = builder.addof1_(au, bu)
    of = builder.and_(noofalbl, ofaubu)
    o3 = builder.selectwadd_(al, bl, const0, of)
    o4 = builder.selectwadd_(au, bu, const255, of)
    o10 = builder.varoutput_(o3)
    o11 = builder.varoutput_(o4)

    program = builder.finish()
    return program


def uint_add_5():
    """
    uinterval add with cisc++ components, more precise
    """
    builder = ProgramBuilder()
    al = builder.varinput_()
    au = builder.varinput_()
    bl = builder.varinput_()
    bu = builder.varinput_()
    const0 = builder.const_(0)
    constMAX = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    select_albl = builder.selectcisc3_(al, au, bl, bu, const0)
    select_aubu = builder.selectcisc4_(al, au, bl, bu, constMAX)
    o10 = builder.varoutput_(select_albl)
    o11 = builder.varoutput_(select_aubu)

    program = builder.finish()
    return program


def tnum_add_1():
    """
    tnum add with risc components
    """
    builder = ProgramBuilder()
    av = builder.varinput_()
    am = builder.varinput_()
    bv = builder.varinput_()
    bm = builder.varinput_()
    sm = builder.add_(am, bm)
    sv = builder.add_(av, bv)
    sigma = builder.add_(sm, sv)
    chi = builder.xor_(sigma, sv)
    mu = builder.or3_(chi, am, bm)
    sv_and_notmu = builder.andwnot_(sv, mu)
    retval = builder.varoutput_(sv_and_notmu)
    retmask = builder.varoutput_(mu)

    program = builder.finish()
    return program


def tnum_sub_1():
    """
    tnum add with risc components
    """
    builder = ProgramBuilder()
    av = builder.varinput_()
    am = builder.varinput_()
    bv = builder.varinput_()
    bm = builder.varinput_()
    dv = builder.sub_(av, bv)
    alpha = builder.add_(dv, am)
    beta = builder.sub_(dv, bm)
    chi = builder.xor_(alpha, beta)
    mu = builder.or3_(chi, am, bm)
    dv_and_notmu = builder.andwnot_(dv, mu)
    retval = builder.varoutput_(dv_and_notmu)
    retmask = builder.varoutput_(mu)

    program = builder.finish()
    return program


def tnum_and_1():
    """
    tnum and with risc components
    """
    builder = ProgramBuilder()
    av = builder.varinput_()
    am = builder.varinput_()
    bv = builder.varinput_()
    bm = builder.varinput_()
    alpha = builder.or_(av, am)
    beta = builder.or_(bv, bm)
    v = builder.and_(av, bv)
    alpha_and_beta = builder.and_(alpha, beta)
    alpha_and_beta_and_notv = builder.andwnot_(alpha_and_beta, v)
    retval = builder.varoutput_(v)
    retmask = builder.varoutput_(alpha_and_beta_and_notv)

    program = builder.finish()
    return program


def tnum_or_1():
    """
    tnum or with risc components
    """
    builder = ProgramBuilder()
    av = builder.varinput_()
    am = builder.varinput_()
    bv = builder.varinput_()
    bm = builder.varinput_()
    zero = builder.const_(0)
    max = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    o1 = builder.or_(av, bv)
    o2 = builder.or_(am, bm)
    o3 = builder.not_(o1)
    o4 = builder.and_(o2, o3)
    retval = builder.varoutput_(o1)
    retmask = builder.varoutput_(o4)

    program = builder.finish()
    return program


def tnum_top():
    """
    tnum add with risc components
    """
    builder = ProgramBuilder()
    av = builder.varinput_()
    am = builder.varinput_()
    bv = builder.varinput_()
    bm = builder.varinput_()
    zero = builder.const_(0)
    max = builder.const_(2**Component.COMPONENT_BV_BITWIDTH - 1)
    retval = builder.varoutput_(zero)
    retmask = builder.varoutput_(max)

    program = builder.finish()
    return program


inject_prog_mappings = {
    "uint_add_1": uint_add_1,
    "uint_add_2": uint_add_2,
    "uint_add_3": uint_add_3,
    "uint_add_4": uint_add_4,
    "uint_add_5": uint_add_5,
    "tnum_add_1": tnum_add_1,
    "tnum_and_1": tnum_and_1,
    "tnum_or_1": tnum_or_1,
    "tnum_sub_1": tnum_sub_1,
    "tnum_top": tnum_top,
}


def inject_prog(progstr):

    return inject_prog_mappings[progstr]()
