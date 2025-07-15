import enum
import z3
from dataclasses import dataclass, field
from abc import ABC, abstractmethod
from typing import ClassVar
import pprint
from collections import OrderedDict

z3.set_pp_option("max_depth", 1000000)
z3.set_pp_option("max_visited", 1000000)
z3.set_pp_option("max_lines", 1000000)


@dataclass
class Component(ABC):
    # unique identifier for components
    component_id: ClassVar[int] = 0
    LINENO_BV_BITWIDTH: ClassVar[int] = 4
    COMPONENT_BV_BITWIDTH: ClassVar[int] = 8

    input_params: list[list[z3.BitVecRef]] = field(init=False)
    output_params: list[list[z3.BitVecRef]] = field(init=False)
    input_linenos: list[z3.BitVecRef] = field(init=False)
    output_linenos: list[z3.BitVecRef] = field(init=False)
    input_lineno_assignments: list[int] = field(init=False)
    output_lineno_assignments: list[int] = field(init=False)
    old_input_lineno_assignments: list[int] = field(init=False)
    old_output_lineno_assignments: list[int] = field(init=False)
    do_init_linenos: bool = True
    do_init_params: bool = False
    instance_id: int = field(init=False)

    def __post_init__(self):

        self.component_id = Component.component_id
        Component.component_id += 1

        # new input/output params are created for each run of the cegis loop
        # instance_id is a unique identifier for input/output params within
        # a component
        self.instance_id = 0

        self.input_params = []
        self.output_params = []
        self.input_linenos = []
        self.output_linenos = []
        self.input_lineno_assignments = []
        self.output_lineno_assignments = []
        self.old_input_lineno_assignments = []
        self.old_output_lineno_assignments = []

    def _init_linenos(self, context):
        self.input_linenos = [
            z3.BitVec(
                f"li{self.component_id}{i}", Component.LINENO_BV_BITWIDTH, ctx=context
            )
            for i in range(self.input_arity())
        ]
        self.output_linenos = [
            z3.BitVec(
                f"lo{self.component_id}", Component.LINENO_BV_BITWIDTH, ctx=context
            )
            for i in range(self.output_arity())
        ]

    @classmethod
    @abstractmethod
    def input_arity(cls):
        raise NotImplementedError

    @classmethod
    @abstractmethod
    def output_arity(cls):
        raise NotImplementedError

    def make_expr(self, instance_id):
        raise NotImplementedError

    def get_expr_str(self):
        raise NotImplementedError

    def update_lineno_assignments(self, model):
        self.old_input_lineno_assignments = self.input_lineno_assignments
        self.old_output_lineno_assignments = self.output_lineno_assignments

        self.input_lineno_assignments = [
            model[input_lineno].as_long() for input_lineno in self.input_linenos
        ]
        self.output_lineno_assignments = [
            model[output_lineno].as_long() for output_lineno in self.output_linenos
        ]

    def restore_lineno_assignments(self):
        self.input_lineno_assignments = [i for i in self.old_input_lineno_assignments]
        self.output_lineno_assignments = [i for i in self.old_output_lineno_assignments]

    def reset_instance_id(self):
        self.instance_id = 0
        self.input_params = []
        self.output_params = []

    def reset_linenos(self):
        self.input_linenos = []
        self.output_linenos = []

    def instantiate_new_input_output_params(self, context):
        new_inputs = [
            z3.BitVec(
                f"I{self.component_id}{i}_{self.instance_id}",
                Component.COMPONENT_BV_BITWIDTH,
                ctx=context,
            )
            for i in range(self.input_arity())
        ]
        self.input_params.append(new_inputs)

        new_outputs = [
            z3.BitVec(
                f"O{self.component_id}_{self.instance_id}",
                Component.COMPONENT_BV_BITWIDTH,
                ctx=context,
            )
            for i in range(self.output_arity())
        ]

        self.output_params.append(new_outputs)
        ret = self.instance_id
        self.instance_id += 1
        return ret

    def get_param_in_bvs(self, instance_id):
        return self.input_params[instance_id]

    def get_param_out_bvs(self, instance_id):
        return self.output_params[instance_id]

    def get_lineno_in_bvs(self):
        return self.input_linenos

    def get_lineno_out_bvs(self):
        return self.output_linenos


@dataclass
class VarInputComponent(Component):

    @classmethod
    def input_arity(cls):
        return 0

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        pass

    def get_expr_str(self):
        return f"var I{self.component_id}[{self.output_lineno_assignments[0]}]"


@dataclass
class VarOutputComponent(Component):

    @classmethod
    def input_arity(cls):
        return 1

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}]"


@dataclass
class ConstComponent(Component):
    const_value: int = 0

    @classmethod
    def input_arity(cls):
        return 0

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        out0_param = self.output_params[instance_id][0]
        return out0_param == self.const_value

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        return f"O{id}[{out0_lineno}] := {self.const_value}"


@dataclass
class NotComponent(Component):

    @classmethod
    def input_arity(cls):
        return 1

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        out0_param = self.output_params[instance_id][0]
        return out0_param == ~in0_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        return f"O{id}[{out0_lineno}] := ~I{id}0[{in0_lineno}]"


class NegComponent(Component):
    @classmethod
    def input_arity(cls):
        return 1

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        out0_param = self.output_params[instance_id][0]
        return out0_param == 1 - in0_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (1 - I{id}0[{in0_lineno}]) & {mask}"


@dataclass
class AddComponent(Component):

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param + in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (I{id}0[{in0_lineno}] + I{id}1[{in1_lineno}]) & {mask}"


@dataclass
class AddComponentCISC1(Component):
    """
    add with overflow
    """

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        p = self.input_params[instance_id][0]
        q = self.input_params[instance_id][1]
        res = self.output_params[instance_id][0]
        return z3.If(
            z3.UGT(p, (p + q)),
            res == 1,
            res == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        p = f"I{id}0[{in0_lineno}]"
        q = f"I{id}1[{in1_lineno}]"
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        p_plus_q = f"({p} + {q}) & {mask}"
        res = f"O{id}[{out0_lineno}]"
        return f"{res} := 1 if ({p} > ({p_plus_q})) else 0"


class AddComponentCISC2(Component):
    """
    add with no overflow
    def add(p, q, res):
        no_overflow = p <= (p + q)
        if (no_overflow):
            res := 1
        else:
            res := 0
    """

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        p = self.input_params[instance_id][0]
        q = self.input_params[instance_id][1]
        res = self.output_params[instance_id][0]
        return z3.If(
            z3.ULE(p, (p + q)),
            res == 1,
            res == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        p = f"I{id}0[{in0_lineno}]"
        q = f"I{id}1[{in1_lineno}]"
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        p_plus_q = f"({p} + {q}) & {mask}"
        res = f"O{id}[{out0_lineno}]"
        return f"{res} := 1 if ({p} <= ({p_plus_q})) else 0"


@dataclass
class SubComponent(Component):

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param - in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (I{id}0[{in0_lineno}] - I{id}1[{in1_lineno}]) & {mask}"


@dataclass
class MulComponent(Component):

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param * in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (I{id}0[{in0_lineno}] * I{id}1[{in1_lineno}]) & {mask}"


@dataclass
class AndComponent(Component):

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param & in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] & I{id}1[{in1_lineno}]"


class AndComponentCISC2(Component):
    """
    o = in1 & ~in2
    """

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param & (~in1_param)

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] & (~I{id}1[{in1_lineno}])"


@dataclass
class AndComponentCISC3(Component):
    """
    3-way bitwise and:
    out = in1 & in2 & in3
    """

    @classmethod
    def input_arity(cls):
        return 3

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        in2_param = self.input_params[instance_id][2]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param & in1_param & in2_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] & I{id}1[{in1_lineno}] & I{id}2[{in2_lineno}]"


@dataclass
class OrComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param | in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] | I{id}1[{in1_lineno}]"


class OrComponentCISC3(Component):
    """
    3-way bitwise or:
    out = in1 | in2 | in3
    """

    @classmethod
    def input_arity(cls):
        return 3

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        in2_param = self.input_params[instance_id][2]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param | in1_param | in2_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] | I{id}1[{in1_lineno}] | I{id}2[{in2_lineno}]"


@dataclass
class XorComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return out0_param == in0_param ^ in1_param

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{id}[{out0_lineno}] := I{id}0[{in0_lineno}] ^ I{id}1[{in1_lineno}]"


@dataclass
class LogicalRightShiftComponent(Component):
    """
    fill new bits with 0
    """

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.And(
            z3.ULT(in1_param, Component.COMPONENT_BV_BITWIDTH),
            out0_param == z3.LShR(in0_param, in1_param),
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (I{id}0[{in0_lineno}] >> I{id}1[{in1_lineno}]) & {mask}"


@dataclass
class ArithmeticLeftShiftComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.And(
            z3.ULT(in1_param, Component.COMPONENT_BV_BITWIDTH),
            out0_param == in0_param << in1_param,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        return f"O{id}[{out0_lineno}] := (I{id}0[{in0_lineno}] << I{id}1[{in1_lineno}]) & {mask}"


@dataclass
class ArithmeticRightShiftComponent(Component):
    """
    fill new bits with old MSB
    """

    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.And(
            z3.ULT(in1_param, Component.COMPONENT_BV_BITWIDTH),
            out0_param == in0_param >> in1_param,
        )

    def get_expr_str(self):
        """
        simulating arsh in python: lambda x, n: (((x ^ 0x80) - 0x80) >> n) & 0xFF
        x ^ 0x80 flips the sign bit, effectively mapping unsigned 8-bit values to signed ones in two's complement.
        Subtracting 0x80 gives the correct signed value in Python.
        >> n then performs an arithmetic right shift.
        & 0xFF wraps the result back to an 8-bit unsigned integer.
        """
        id = self.component_id
        out0_lineno = o = self.output_lineno_assignments[0]
        in0_lineno = x = self.input_lineno_assignments[0]
        in1_lineno = n = self.input_lineno_assignments[1]
        mask = f"{hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        msb = f"{hex(2**(Component.COMPONENT_BV_BITWIDTH - 1))}"
        return f"O{id}[{o}] := (((I{id}0{x} ^ {msb}) - {msb}) >> I{id}1{n}) & {mask}"


@dataclass
class UnsignedGreaterOrEqualComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            z3.UGE(
                in0_param,
                in1_param,
            ),
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] >= I{id}1[{in1_lineno}]) else 0"


@dataclass
class SignedGreaterOrEqualComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            in0_param >= in1_param,
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        """
        TODO: fix this
        """
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] >= I{id}1[{in1_lineno}]) else 0"


@dataclass
class UnsignedGreaterThanComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            z3.UGT(
                in0_param,
                in1_param,
            ),
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] > I{id}1[{in1_lineno}]) else 0"


@dataclass
class SignedGreaterThanComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            in0_param > in1_param,
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        """
        TODO: fix this
        """
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] > I{id}1[{in1_lineno}]) else 0"


@dataclass
class UnsignedLessThanComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            z3.ULT(in0_param, in1_param),
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] < I{id}1[{in1_lineno}]) else 0"


@dataclass
class SignedLessThanComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            in0_param < in1_param,
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        """
        TODO: fix this
        """
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] < I{id}1[{in1_lineno}]) else 0"


@dataclass
class UnsignedLessOrEqualComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            z3.ULE(in0_param, in1_param),
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] <= I{id}1[{in1_lineno}]) else 0"


@dataclass
class SignedLessOrEqualComponent(Component):
    @classmethod
    def input_arity(cls):
        return 2

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            in0_param <= in1_param,
            out0_param == 1,
            out0_param == 0,
        )

    def get_expr_str(self):
        """
        TODO: fix this
        """
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        return f"O{self.component_id}[{out0_lineno}] := 1 if (I{id}0[{in0_lineno}] <= I{id}1[{in1_lineno}]) else 0"


@dataclass
class SelectComponent(Component):
    """
    def select_(cond, p, q):
        res := p if (cond == 1) else q
    """

    @classmethod
    def input_arity(cls):
        return 3

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        in0_param = self.input_params[instance_id][0]
        in1_param = self.input_params[instance_id][1]
        in2_param = self.input_params[instance_id][2]
        out0_param = self.output_params[instance_id][0]
        return z3.If(
            in0_param == 1,
            out0_param == in1_param,
            out0_param == in2_param,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        return f"O{self.component_id}[{out0_lineno}] := I{id}1[{in1_lineno}] if (I{id}0[{in0_lineno}] == 1) else I{id}2[{in2_lineno}]"


@dataclass
class SelectComponentCISC2(Component):
    """
    select with add on flag:
    def selectwadd_(p, q, const, flag, res):
        if (flag):
            res := const
        else:
            res := p + q
    """

    @classmethod
    def input_arity(cls):
        return 4

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        p = self.input_params[instance_id][0]
        q = self.input_params[instance_id][1]
        const = self.input_params[instance_id][2]
        ovflw = self.input_params[instance_id][3]
        res = self.output_params[instance_id][0]
        return z3.If(
            ovflw == 1,
            res == const,
            res == p + q,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        in3_lineno = self.input_lineno_assignments[3]
        p = f"I{id}0[{in0_lineno}]"
        q = f"I{id}1[{in1_lineno}]"
        p_plus_q = f"({p} + {q}) & {hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        const = f"I{id}2[{in2_lineno}]"
        ovflw = f"I{id}3[{in3_lineno}]"
        res = f"O{self.component_id}[{out0_lineno}]"
        return f"{res} := {const} if ({ovflw} == 1) else ({p_plus_q})"


@dataclass
class SelectComponentCISC5(Component):
    """
    select with sub on flag:
    def selectwsub_(p, q, const, flag, res):
        if (flag):
            res := const
        else:
            res := p - q
    """

    @classmethod
    def input_arity(cls):
        return 4

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        p = self.input_params[instance_id][0]
        q = self.input_params[instance_id][1]
        const = self.input_params[instance_id][2]
        ovflw = self.input_params[instance_id][3]
        res = self.output_params[instance_id][0]
        return z3.If(
            ovflw == 1,
            res == const,
            res == p - q,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        in3_lineno = self.input_lineno_assignments[3]
        p = f"I{id}0[{in0_lineno}]"
        q = f"I{id}1[{in1_lineno}]"
        p_minus_q = f"({p} - {q}) & {hex(2**Component.COMPONENT_BV_BITWIDTH - 1)}"
        const = f"I{id}2[{in2_lineno}]"
        ovflw = f"I{id}3[{in3_lineno}]"
        res = f"O{self.component_id}[{out0_lineno}]"
        return f"{res} := {const} if ({ovflw} == 1) else ({p_minus_q})"


@dataclass
class SelectComponentCISC3(Component):
    """
    select with add al + bl on (overflow and no overflow)

    def select(al, au, bl, bu, const, res):
        if (al <= al + bl) and (au > au + bu)
            res := const
        else:
            res := al + bl
    """

    @classmethod
    def input_arity(cls):
        return 5

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        al = self.input_params[instance_id][0]
        au = self.input_params[instance_id][1]
        bl = self.input_params[instance_id][2]
        bu = self.input_params[instance_id][3]
        const = self.input_params[instance_id][4]
        res = self.output_params[instance_id][0]
        return z3.If(
            z3.And(z3.ULE(al, al + bl), z3.UGT(au, au + bu)),
            res == const,
            res == al + bl,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        in3_lineno = self.input_lineno_assignments[3]
        in4_lineno = self.input_lineno_assignments[4]
        al = f"I{id}0[{in0_lineno}]"
        au = f"I{id}1[{in1_lineno}]"
        bl = f"I{id}2[{in2_lineno}]"
        bu = f"I{id}3[{in3_lineno}]"
        const = f"I{id}4[{in4_lineno}]"
        res = f"O{self.component_id}[{out0_lineno}]"
        bvmask = hex(2**Component.COMPONENT_BV_BITWIDTH - 1)
        l_noovf = f"({al} <= (({al} + {bl}) & {bvmask}))"
        u_ovf = f"({au} > (({au} + {bu}) & {bvmask}))"
        l_noovf_u_ovf = f"({l_noovf} and {u_ovf})"
        return f"{res} := {const} if ({l_noovf_u_ovf}) else (({al} + {bl}) & {bvmask})"


@dataclass
class SelectComponentCISC4(Component):
    """
    select with add au + bu on (overflow and no overflow)

    def select(al, au, bl, bu, const, res):
        if (al <= al + bl) and (au > au + bu)
            res := const
        else:
            res := au + bu
    """

    @classmethod
    def input_arity(cls):
        return 5

    @classmethod
    def output_arity(cls):
        return 1

    def make_expr(self, instance_id):
        al = self.input_params[instance_id][0]
        au = self.input_params[instance_id][1]
        bl = self.input_params[instance_id][2]
        bu = self.input_params[instance_id][3]
        const = self.input_params[instance_id][4]
        res = self.output_params[instance_id][0]
        return z3.If(
            z3.And(z3.ULE(al, al + bl), z3.UGT(au, au + bu)),
            res == const,
            res == au + bu,
        )

    def get_expr_str(self):
        id = self.component_id
        out0_lineno = self.output_lineno_assignments[0]
        in0_lineno = self.input_lineno_assignments[0]
        in1_lineno = self.input_lineno_assignments[1]
        in2_lineno = self.input_lineno_assignments[2]
        in3_lineno = self.input_lineno_assignments[3]
        in4_lineno = self.input_lineno_assignments[4]
        al = f"I{id}0[{in0_lineno}]"
        au = f"I{id}1[{in1_lineno}]"
        bl = f"I{id}2[{in2_lineno}]"
        bu = f"I{id}3[{in3_lineno}]"
        const = f"I{id}4[{in4_lineno}]"
        res = f"O{self.component_id}[{out0_lineno}]"
        bvmask = hex(2**Component.COMPONENT_BV_BITWIDTH - 1)
        l_noovf = f"({al} <= (({al} + {bl}) & {bvmask}))"
        u_ovf = f"({au} > (({au} + {bu}) & {bvmask}))"
        l_noovf_u_ovf = f"({l_noovf} and {u_ovf})"
        return f"{res} := {const} if ({l_noovf_u_ovf}) else (({au} + {bu}) & {bvmask})"


if __name__ == "__main__":
    components = [
        AndComponent,
        (ConstComponent, 1),
        SubComponent,
        AndComponent,
    ]

    pprint.pprint(components)


"""
there are two types of duplicate components possible

-one for philib in finite synthesis, where you need to instantiate 
components multiple times, with the same lineno

-other when you have duplicate components in your component library, 
these components have different linenos
"""
