import z3
from component import *
from collections import namedtuple
import random
import inspect

"""
A library of program specifications for abstract operators
"""
AbstractSpecification = namedtuple(
    "spec",
    [
        "conc_func_semantics",
        "abs_wf_semantics",
        "abs_contains_semantics",
        "eg_generator_func",
        "abs_op_input_arity",
        "abs_op_output_arity",
    ],
)


def init_seed(seed):
    random.seed(seed)


class UnsignedInterval:

    @staticmethod
    def contains(x, Pl, Pu):
        return z3.And(z3.ULE(Pl, x), z3.ULE(x, Pu))

    @staticmethod
    def wellformed(Pl, Pu):
        return z3.ULE(Pl, Pu)

    @staticmethod
    def get_random_abs_val():
        MAX_UINT = 2**Component.COMPONENT_BV_BITWIDTH - 1
        while True:
            Pl = z3.BitVecVal(
                random.randint(0, MAX_UINT), Component.COMPONENT_BV_BITWIDTH
            )
            Pu = z3.BitVecVal(
                random.randint(0, MAX_UINT), Component.COMPONENT_BV_BITWIDTH
            )
            if z3.is_true(z3.simplify(UnsignedInterval.wellformed(Pl, Pu))):
                return (Pl, Pu)

    @staticmethod
    def get_random_conc_in_absval(Pl, Pu):
        MAX_UINT = 2**Component.COMPONENT_BV_BITWIDTH - 1
        while True:
            x = random.randint(0, MAX_UINT)
            if z3.is_true(z3.simplify(UnsignedInterval.contains(x, Pl, Pu))):
                return x


def p006_uint_add(components, use_cisc):
    # o6 = 0
    # o7 = 255
    # o1 = a.l + b.l
    # o2 = a.u + b.u
    # o3 = a.l > o1
    # o4 = a.u > o2
    # o5 = o3 | o4
    # o8 = ite(o5, o6, o1)
    # o9 = ite(o5, o7, o2)
    # return (o8, o9)
    if not use_cisc:
        components.extend(
            [
                (ConstComponent, 0),
                (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
                AddComponent,
                AddComponent,
                UnsignedGreaterThanComponent,
                UnsignedGreaterThanComponent,
                OrComponent,
                SelectComponent,
                SelectComponent,
            ]
        )
    # else:
    #     components.extend(
    #         [
    #             (ConstComponent, 0),
    #             (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
    #             SelectComponentCISC3,
    #             SelectComponentCISC4,
    #         ]
    #     )
    else:
        components.extend(
            [
                (ConstComponent, 0),
                (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
                AddComponentCISC2,
                AddComponentCISC1,
                AndComponent,
                SelectComponentCISC2,
                SelectComponentCISC2,
            ]
        )

    def conc_func(a, b):
        return (2**Component.COMPONENT_BV_BITWIDTH - 1) & a + b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 + in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = UnsignedInterval.get_random_abs_val()
            concval = UnsignedInterval.get_random_conc_in_absval(*absval)
            absvals.extend([a.as_long() for a in absval])
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]

        # TODO return a dictionary directly
        # positive_eg_dict = {}
        # positive_eg_dict[tuple(absvals)] = conc_out
        # return positive_eg_dict

        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=UnsignedInterval.wellformed,
        abs_contains_semantics=UnsignedInterval.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p008_uint_sub(components, use_cisc):

    # zero = 0
    # max = 255
    # ovf = al < bu
    # lo = al - bu
    # hi = au - bl
    # retlo = ite(ovf, zero, lo)
    # rethi = ite(ovf, max, hi)
    # return (retlo, rethi)
    if not use_cisc:
        components.extend(
            [
                (ConstComponent, 0),
                (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
                UnsignedLessThanComponent,
                SubComponent,
                SubComponent,
                SelectComponent,
                SelectComponent,
            ]
        )
    else:
        components.extend(
            [
                (ConstComponent, 0),
                (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
                UnsignedLessThanComponent,
                UnsignedGreaterOrEqualComponent,
                AndComponent,
                SelectComponentCISC5,
                SelectComponentCISC5,
            ]
        )

    def conc_func(a, b):
        return (2**Component.COMPONENT_BV_BITWIDTH - 1) & a - b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 - in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = UnsignedInterval.get_random_abs_val()
            concval = UnsignedInterval.get_random_conc_in_absval(*absval)
            absvals.extend([a.as_long() for a in absval])
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]

        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=UnsignedInterval.wellformed,
        abs_contains_semantics=UnsignedInterval.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p007_uint_abs(components, use_cisc):
    # o1 = uge(0, a.l)
    # o2 = 0
    # o3 = o2 - a.r
    # o4 =
    # o5 = o3 | o4
    # o6 = 0
    # o7 = 255
    # o8 = ite(o5, o6, o1)
    # o9 = ite(o5, o7, o2)
    # return (o8, o9)
    components.extend(
        [
            AddComponent,
            AddComponent,
            UnsignedGreaterThanComponent,
            UnsignedGreaterThanComponent,
            OrComponent,
            (ConstComponent, 0),
            (ConstComponent, 2**Component.COMPONENT_BV_BITWIDTH - 1),
            SelectComponent,
            SelectComponent,
        ]
    )

    def conc_func(a, b):
        return (2**Component.COMPONENT_BV_BITWIDTH - 1) & a + b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 + in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = UnsignedInterval.get_random_abs_val()
            concval = UnsignedInterval.get_random_conc_in_absval(*absval)
            absvals.extend([a.as_long() for a in absval])
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]

        # TODO return a dictionary directly
        # positive_eg_dict = {}
        # positive_eg_dict[tuple(absvals)] = conc_out
        # return positive_eg_dict

        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=UnsignedInterval.wellformed,
        abs_contains_semantics=UnsignedInterval.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


class Tnum:
    @staticmethod
    def contains(x, Pv, Pm):
        return x & ~Pm == Pv

    @staticmethod
    def wellformed(Pv, Pm):
        return Pv & Pm == 0

    @staticmethod
    def get_random_abs_val():
        MAX_UINT = 2**Component.COMPONENT_BV_BITWIDTH - 1
        while True:
            Pv = random.randint(0, MAX_UINT)
            Pm = random.randint(0, MAX_UINT)
            if Tnum.wellformed(Pv, Pm):
                return (Pv, Pm)

    @staticmethod
    def get_random_conc_in_absval(Pv, Pm):
        MAX_UINT = 2**Component.COMPONENT_BV_BITWIDTH - 1
        while True:
            x = random.randint(0, MAX_UINT)
            if Tnum.contains(x, Pv, Pm):
                return x


def p001_tnum_and(components, use_cisc):
    # o1 = a.value | a.mask;
    # o2 = b.value | b.mask;
    # o3 = a.value & b.value;
    # o4 = o1 & o2;
    # o5 = ~o3;
    # o6 = o4 & o5;
    # return TNUM(o3,  o6);
    # lambda av, am, bv, bm : ((av & bv), (((av | am) & (bv | bm)) & ~((av & bv))))
    if not use_cisc:
        components.extend(
            [
                OrComponent,
                OrComponent,
                AndComponent,
                NotComponent,
                AndComponent,
                AndComponent,
            ]
        )
    else:
        components.extend(
            [
                OrComponent,
                OrComponent,
                AndComponent,
                AndComponentCISC2,
            ]
        )

    def conc_func(a, b):
        return a & b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 & in1

    def get_positive_example():

        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = Tnum.get_random_abs_val()
            concval = Tnum.get_random_conc_in_absval(*absval)
            absvals.extend(absval)
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]
        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=Tnum.wellformed,
        abs_contains_semantics=Tnum.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p002_tnum_or(components, use_cisc):
    # o1 = a.value | b.value;
    # o2 = a.mask | b.mask;
    # o3 = ~o1
    # o4 = o2 & o3
    # return TNUM(o1, o4);
    # lambda i0, i1, i2, i3 : (0xFF & ((i0 | i2)), 0xFF & (((~(i0 | i2)) & (i1 | i3))))
    components.extend(
        [
            OrComponent,
            OrComponent,
            NotComponent,
            AndComponent,
        ]
    )

    def conc_func(a, b):
        return a | b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 | in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = Tnum.get_random_abs_val()
            concval = Tnum.get_random_conc_in_absval(*absval)
            absvals.extend(absval)
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]
        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=Tnum.wellformed,
        abs_contains_semantics=Tnum.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p003_tnum_xor(components, use_cisc):
    # v = a.value ^ b.value;
    # mu = a.mask | b.mask;
    # negmu = ~mu
    # retval = v & negmu
    # retmask = mu
    # return TNUM(retval, retmask);
    components.extend(
        [
            XorComponent,
            OrComponent,
            AndComponent,
            NotComponent,
        ]
    )

    def conc_func(a, b):
        return a ^ b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 ^ in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = Tnum.get_random_abs_val()
            concval = Tnum.get_random_conc_in_absval(*absval)
            absvals.extend(absval)
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]
        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=Tnum.wellformed,
        abs_contains_semantics=Tnum.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p004_tnum_add(components, use_cisc):
    # sm = a.mask + b.mask;
    # sv = a.value + b.value;
    # sigma = sm + sv;
    # chi = sigma ^ sv;
    # ambm = a.mask | b.mask;
    # mu = chi | ambm;
    # negmu = ~mu
    # retval = sv & negmu
    # retmask = mu
    # return TNUM(retval, retmask);
    # tnum_add_kernel = lambda av, am, bv, bm : ((0xff & ((av + bv) & (~((((am + bm) + (av + bv)) ^ (av + bv)) | am | bm)))), (0xff & ((((am + bm) + (av + bv)) ^ (av + bv)) | am | bm)))

    if not use_cisc:
        components.extend(
            [
                AddComponent,
                AddComponent,
                AddComponent,
                XorComponent,
                OrComponent,
                OrComponent,
                NotComponent,
                AndComponent,
            ]
        )
    else:
        components.extend(
            [
                AddComponent,
                AddComponent,
                AddComponent,
                XorComponent,
                OrComponentCISC3,
                AndComponentCISC2,
            ]
        )

    def conc_func(a, b):
        return (2**Component.COMPONENT_BV_BITWIDTH - 1) & a + b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 + in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = Tnum.get_random_abs_val()
            concval = Tnum.get_random_conc_in_absval(*absval)
            absvals.extend(absval)
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]
        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=Tnum.wellformed,
        abs_contains_semantics=Tnum.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


def p005_tnum_sub(components, use_cisc):

    # dv = av - bv
    # alpha = dv + am
    # beta = dv - bm
    # chi = alpha ^ beta
    # mu = chi | am | bm
    # retval = dv & ~mu
    # retmask = mu
    # return TNUM(retval, retmask)
    # tnum_sub_kernel = lambda av, am, bv, bm: (((av - bv) & (~((((av - bv) + am) ^ ((av - bv) - bm)) | (am | bm)))), ((((av - bv) + am) ^ ((av - bv) - bm)) | (am | bm)))

    if not use_cisc:
        components.extend(
            [
                SubComponent,
                AddComponent,
                SubComponent,
                XorComponent,
                OrComponent,
                OrComponent,
                NotComponent,
                AndComponent,
            ]
        )
    else:
        components.extend(
            [
                SubComponent,
                AddComponent,
                SubComponent,
                XorComponent,
                OrComponentCISC3,
                AndComponentCISC2,
            ]
        )

    def conc_func(a, b):
        return (2**Component.COMPONENT_BV_BITWIDTH - 1) & a - b

    def conc_func_semantics(in0, in1, out0):
        return out0 == in0 - in1

    def get_positive_example():
        conc_op_arity = len(inspect.signature(conc_func).parameters)
        absvals = []
        concvals = []
        for i in range(conc_op_arity):
            absval = Tnum.get_random_abs_val()
            concval = Tnum.get_random_conc_in_absval(*absval)
            absvals.extend(absval)
            concvals.append(concval)
        conc_out = conc_func(*concvals)
        positve_eg = absvals + [conc_out]
        return tuple(positve_eg)

    return AbstractSpecification(
        conc_func_semantics=conc_func_semantics,
        abs_wf_semantics=Tnum.wellformed,
        abs_contains_semantics=Tnum.contains,
        eg_generator_func=get_positive_example,
        abs_op_input_arity=4,
        abs_op_output_arity=2,
    )


abs_prog_spec_mappings = {
    "tnum_and": p001_tnum_and,
    "tnum_or": p002_tnum_or,
    "tnum_xor": p003_tnum_xor,
    "tnum_add": p004_tnum_add,
    "tnum_sub": p005_tnum_sub,
    "uint_add": p006_uint_add,
    "uint_sub": p008_uint_sub,
}


if __name__ == "__main__":
    components_ = []
    (
        conc_func_semantics,
        abs_wf_semantics,
        abs_contains_semantics,
        eg_generator_func,
        abs_op_input_arity,
        abs_op_output_arity,
    ) = abs_prog_spec_mappings["tnum_add"](components_)

    x, y, z = z3.BitVecs("x y z", 8)
    print(conc_func_semantics(x, y, z))
    eg = eg_generator_func()
    print(eg)
    eg_conc = eg[-1]
    Rv, Rm = z3.BitVecs("Rv Rm", 8)
    print(abs_wf_semantics(Rv, Rm))
    print(abs_contains_semantics(eg_conc, Rv, Rm))
