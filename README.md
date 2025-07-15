# Vayu: Synthesizing Precise Abstract Operators for the eBPF Verifier

Vayu automatically synthesizes sound and precise abstract operators for use in the eBPF
verifier. Given a concrete eBPF operator f, we seek an abstract operator F that
conservatively over-approximates f (sound) while excluding concrete values that will
never occur at runtime as an output of f (precise).

Vayu contains two CEGIS loops and proceeds in two steps. Step A uses a CEGIS procedure
with a soundness specification to synthesize a sound candidate operator. Step B then
iteratively refines this candidate also using a CEGIS procedure, guided by a precision
specification, to produce a more precise operator that remains sound.

Vayu uses the z3 SMT Solver:
```
pip install z3-solver
```

The current abstract domains supported are: `tnum` (tristate numbers) and `uint`
(unsigned intervals). The specific operators supported are:

|          |         |
| -------- | ------- |
| tnum     | add, sub, and, or, xor     |
| uint     | add, sub                   |
|          |         |

To run, we use the python script `cegis_abs.py`. We need to specify the combination
of the domain + operator, together. For e.g., `tnum_xor`

```
python3 cegis_abs.py --spec tnum_xor
```

If the synthesis succeeds, you might get an output with an operator, like so:

```
final synthezied program lambda:
lambda P, Q, R, S : (((R ^ P) & (~(Q | S))), (Q | S))
```

The output shows a python-lambda syntax representation of the synthesized operator,
which has four inputs and two outputs.

