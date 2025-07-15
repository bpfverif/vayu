import z3
from component import *
from collections import namedtuple

"""
A library of program specifications
"""

Specification = namedtuple("spec", ["function", "input_arity", "output_arity"])


def p1(components):
    """turn off rightmost "1" bit"""
    # 1 o1:=bvsub (x,1)
    # 2 res:=bvand (x,o1)
    components.extend(
        [
            AndComponent,
            (ConstComponent, 1),
            SubComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):

        prog_input = prog_inputs[0]
        prog_output = prog_outputs[0]

        bw = Component.COMPONENT_BV_BITWIDTH
        formula = []
        for i in range(0, bw):
            if i == bw - 1:
                l = z3.Int("temp")
                m = z3.Extract(i, i, prog_input)
                r = z3.Extract(i - 1, 0, prog_input)
                f = z3.Implies(z3.And(m == 1, r == 0), prog_output == 0)
            elif i == 0:
                l = z3.Extract(bw - 1, i + 1, prog_input)
                m = z3.Extract(i, i, prog_input)
                r = z3.Int("temp")
                f = z3.Implies(m == 1, prog_output == z3.Concat(l, z3.BitVecVal(0, 1)))
            else:
                l = z3.Extract(bw - 1, i + 1, prog_input)
                m = z3.Extract(i, i, prog_input)
                r = z3.Extract(i - 1, 0, prog_input)
                f = z3.Implies(
                    z3.And(m == 1, r == 0),
                    prog_output == z3.Concat(l, z3.BitVecVal(0, 1), r),
                )
            formula.append(f)
        prog_spec_rest = z3.And(formula)
        prog_spec_0 = z3.Implies(prog_input == 0, prog_output == 0)
        prog_spec = z3.And(prog_spec_0, prog_spec_rest)

        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=1)


def p9(components):
    """absolute value"""
    # 1 o1:=bvshr (x,7)
    # 2 o2:=bvxor (x,o1)
    # 3 res:=bvsub (o2,o1)
    components.extend(
        [
            (ConstComponent, Component.COMPONENT_BV_BITWIDTH - 1),
            ArithmeticRightShiftComponent,
            # LogicalRightShiftComponent,
            XorComponent,
            SubComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):

        prog_input = prog_inputs[0]
        prog_output = prog_outputs[0]

        prog_spec = []
        prog_spec.append(z3.Implies(prog_input >= 0, prog_output == prog_input))
        prog_spec.append(z3.Implies(prog_input < 0, prog_output == -prog_input))
        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=1)


def p13(components):
    """sign function"""
    # 1 o1:=bvshr (x,31)
    # 2 o2:= bvneg(x)
    # 3 o3:=bvshr (o2,31)
    # 4 res:=bvor (o1,o3)
    # lambda x: (x >> 7) | (0 - x) >> 7))
    components.extend(
        [
            (ConstComponent, Component.COMPONENT_BV_BITWIDTH - 1),
            ArithmeticRightShiftComponent,
            (ConstComponent, 0),
            SubComponent,
            LogicalRightShiftComponent,
            OrComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):
        prog_input = prog_inputs[0]
        prog_output = prog_outputs[0]

        prog_spec = []
        prog_spec.append(z3.Implies(prog_input == 0, prog_output == 0))
        prog_spec.append(z3.Implies(prog_input > 0, prog_output == 1))
        prog_spec.append(z3.Implies(prog_input < 0, prog_output == -1))

        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=1)


def p16(components):
    """max of two unsigned integers"""
    # 1 o1:=bvxor (x,y)
    # 2 o2:=bvneg (bvuge (x,y))
    # 3 o3:=bvand (o1,o2)
    # 4 res:=bvxor (o3,y)
    # lambda x, y: ((x ^ y) & (0 - (1 if x > y else 0))) ^ y
    # lambda x, y: x ^ ((0 - (1 if x > y else 0)) & (x ^ y))
    components.extend(
        [
            (ConstComponent, 0),
            XorComponent,
            UnsignedGreaterOrEqualComponent,
            SubComponent,
            AndComponent,
            XorComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):
        prog_input1 = prog_inputs[0]
        prog_input2 = prog_inputs[1]
        prog_output = prog_outputs[0]
        prog_spec = []
        prog_spec.append(
            z3.If(
                z3.UGE(prog_input1, prog_input2),
                prog_output == prog_input1,
                prog_output == prog_input2,
            )
        )
        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=2, output_arity=1)


def p17(components):
    """turn off a string of  rightmost consecutive 1's"""
    # 1 o1:=bvsub (x,1)
    # 2 o2:=bvor (x,o1)
    # 3 o3:=bvadd (o2,1)
    # 4 res:=bvand (o3,x)
    components.extend(
        [
            AndComponent,
            (ConstComponent, 1),
            SubComponent,
            OrComponent,
            AddComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):
        prog_input = prog_inputs[0]
        prog_output = prog_outputs[0]

        prog_spec = []
        o1 = prog_input - 1
        o2 = o1 | prog_input
        o3 = o2 + 1
        o4 = o3 & prog_input
        prog_spec.append(prog_output == o4)

        prog_spec = z3.And(prog_spec)

        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=1)


def pt1(components):
    """minus 1 (for testing)"""

    components.extend(
        [
            (ConstComponent, 1),
            SubComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):

        prog_input = prog_inputs[0]
        prog_output = prog_outputs[0]

        prog_spec = []
        prog_spec.append(prog_output == prog_input - 1)
        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=1)


def pt2(components):
    """
    max of two integers + min of two integers (only for testing, components don't work)
    """
    components.extend(
        [
            (ConstComponent, 0),
            NotComponent,
            XorComponent,
            SelectComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):
        prog_input1 = prog_inputs[0]
        prog_input2 = prog_inputs[1]
        prog_output1 = prog_outputs[0]
        prog_output2 = prog_outputs[1]
        prog_spec = []
        prog_spec.append(
            z3.If(
                z3.UGE(prog_input1, prog_input2),
                prog_output1 == prog_input1,
                prog_output1 == prog_input2,
            )
        )
        prog_spec.append(
            z3.If(
                z3.UGE(prog_input1, prog_input2),
                prog_output2 == prog_input2,
                prog_output2 == prog_input1,
            )
        )
        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=2, output_arity=2)


def pt3(components):
    """absolute value + sign function (testing multiple outputs)"""

    components.extend(
        [
            (ConstComponent, Component.COMPONENT_BV_BITWIDTH - 1),
            ArithmeticRightShiftComponent,
            XorComponent,
            SubComponent,
            ArithmeticRightShiftComponent,
            (ConstComponent, 0),
            SubComponent,
            LogicalRightShiftComponent,
            OrComponent,
        ]
    )

    def spec(prog_inputs: list, prog_outputs: list):
        prog_input = prog_inputs[0]
        prog_output0 = prog_outputs[0]  # sign
        prog_output1 = prog_outputs[1]  # absval

        prog_spec = []
        prog_spec.append(
            z3.Implies(prog_input == 0, z3.And(prog_output0 == 0, prog_output1 == 0))
        )
        prog_spec.append(
            z3.Implies(
                prog_input > 0, z3.And(prog_output0 == 1, prog_output1 == prog_input)
            )
        )
        prog_spec.append(
            z3.Implies(
                prog_input < 0, z3.And(prog_output0 == -1, prog_output1 == -prog_input)
            )
        )

        prog_spec = z3.And(prog_spec)
        return prog_spec

    return Specification(function=spec, input_arity=1, output_arity=2)


def get_prog_spec(components):
    # return p1(components)  # turn off rightmost 1 bit
    # return p9(components)  # absolute value
    return p13(components)  # sign function
    # return p16(components)  # max of two integers
    # return p17(components)  # turn off a string of rightmost consecutive 1's
    # return pt1(components)
    # return pt2(components)
    # return pt3(components)
