"""Build and replay the 16-input OR-only encoders, including the zero baseline."""

from functools import reduce


def positive():
    gates = []
    terms = {subset: [subset] for subset in range(1, 16)}
    outputs = {}
    for subset in sorted(terms, key=int.bit_count, reverse=True):
        wire, *others = terms[subset]
        for other in others:
            gates.append((wire, other))
            wire = 15 + len(gates)
        least = subset & -subset
        if least == subset:
            outputs[least.bit_length() - 1] = wire
        else:
            terms[least].append(wire)
            terms[subset - least].append(wire)
    return gates, [outputs[i] for i in range(4)]


def bipolar():
    gates = []
    def either(left, right):
        gates.append((left, right))
        return 15 + len(gates)
    axes = [[reduce(either, (4*i+j for j in range(4))) for i in range(4)],
            [reduce(either, (4*i+j for i in range(4))) for j in range(4)]]
    outputs = []
    for bit in range(4):
        groups = axes[1 - bit//2]
        for polarity in (1, 0):
            outputs.append(reduce(either, (groups[i] for i in range(4) if i>>(bit%2)&1==polarity)))
    return gates, outputs


def check():
    for maker, size in [(positive, 22), (bipolar, 32)]:
        gates, outputs = maker()
        if len(gates) != size:
            raise AssertionError(size)
        for p in range(-1, 16):
            values = [v == p for v in range(16)]
            for a,b in gates:
                values.append(values[a] or values[b])
            expected = [] if p < 0 else [(p >> i) & 1 for i in range(4)]
            if p < 0:
                expected = [0] * len(outputs)
            elif maker == bipolar:
                expected = [item for bit in expected for item in (bit, 1-bit)]
            if [values[v] for v in outputs] != expected:
                raise AssertionError((maker.__name__, p))
        print(f"{maker.__name__}: {len(outputs)} outputs, {size} gates, zero and all 16 one-hot rows checked")


if __name__ == "__main__":
    check()
