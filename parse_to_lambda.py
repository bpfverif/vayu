import re
from component import Component


def parse_program(program_str):
    lines = program_str.strip().split("\n")
    assignments = {}

    for line in lines:
        match = re.match(r"(\w+)\[(\d+)\] := (.+)", line)
        if match:
            var, index, expr = match.groups()
            assignments[int(index)] = (var, expr)

    return assignments


def replace_variables(expr, assignments, inputs):
    def replacer(match):
        var, index = match.groups()
        index = int(index)
        if var.startswith("I") and index in inputs:
            return inputs[index]
        return f"({assignments[index][1]})" if index in assignments else var

    pattern = re.compile(r"(\w+)\[(\d+)\]")
    while pattern.search(expr):
        expr = pattern.sub(replacer, expr)

    return expr


def get_prog_outputs(program_str, num_outputs):
    lines = program_str.strip().split("\n")
    outputs = []

    for line in lines[-num_outputs:]:
        match = re.match(r"(O[0-9]*)(\[[0-9]*\]\s:=\s)(.*)", line)
        if match:
            output = match.groups()[0]
            outputs.append(output)
            # outputs[int(index)] = (var, expr)

    return outputs


def construct_lambda(program_str, num_inputs, num_outputs):
    assignments = parse_program(program_str)
    # inputs = {i: f"i{i}" for i in range(num_inputs)}
    inputs = {
        0: "P",
        1: "Q",
        2: "R",
        3: "S",
    }
    outputs_from_program_str = get_prog_outputs(program_str, num_outputs)

    output_expressions = {}
    for idx, (var, expr) in assignments.items():
        if var in outputs_from_program_str:
            output_expressions[var] = replace_variables(expr, assignments, inputs)

    inputs_str = ", ".join(inputs.values())
    outputs_str = ", ".join(f"{v}" for v in output_expressions.values())
    lambda_expr = f"lambda {inputs_str} : ({outputs_str})"
    return lambda_expr


if __name__ == "__main__":
    program_str = """\
var I0[0]
var I1[1]
var I2[2]
var I3[3]
O4[4] := I40[0] | I41[0]
O8[5] := I80[4] | I81[0]
O6[6] := ~I60[5]
O7[7] := I70[1] & I71[2]
O5[8] := I50[4] | I51[0]
O9[9] := I40[0] | I41[0]
O10[10] := ~((I40[0] | I41[0]) | I81[0])"""

    lambda_function = construct_lambda(program_str, 4, 2)
    print(lambda_function)
