"""Construct and verify 19-gate dominance-admissible certificates for the four rows."""
from itertools import combinations, product
from pathlib import Path
import json

T = 16383
root = Path(__file__).parent
rows = json.loads((root / "seed_tables.json").read_text())


def build(row, stars):
    wires = row[:]
    gates = []

    def add(op, a, b):
        w = wires[a] & wires[b] if op == "AND" else wires[a] | wires[b]
        if any(((s ^ T) & (w ^ T)) == (s ^ T) for s in wires):
            raise ValueError
        gates.append([op, a, b, w])
        wires.append(w)
        return len(wires) - 1

    try:
        sides = []
        for center, neighbors in stars.items():
            if not neighbors:
                return
            part = neighbors[0]
            for x in neighbors[1:]:
                part = add("OR", part, x)
            sides.append((center, part))
        parts = [add("AND", a, b) for a, b in sides]
        left = parts[0]
        for right in parts[1:]:
            left = add("OR", left, right)
        if len(gates) == 19 and wires[left] == T:
            return gates
    except ValueError:
        return


def search(row):
    verts = [i for i, w in enumerate(row) if w]
    edges = [tuple(i for i in verts if (row[i] >> j) & 1) for j in range(14)]
    for cover in combinations(verts, 6):
        options = [tuple(i for i in edge if i in cover) for edge in edges]
        if any(not choices for choices in options):
            continue
        for centers in product(*options):
            stars = {c: [] for c in cover}
            for edge, center in zip(edges, centers):
                stars[center].append(next(v for v in edge if v != center))
            certificate = build(row, stars)
            if certificate:
                return certificate
    raise RuntimeError("No admissible 19-gate construction found.")


if __name__ == "__main__":
    certificates = [search(row) for row in rows]
    for row, gates in zip(rows, certificates):
        outputs = row[:]
        for op, a, b, w in gates:
            assert (outputs[a] & outputs[b] if op == "AND" else outputs[a] | outputs[b]) == w
            assert all(((s^T) & (w^T)) != (s^T) for s in outputs)
            outputs.append(w)
        assert len(gates) == 19 and outputs[-1] == T
    (root / "star_upper.json").write_text(json.dumps(certificates,indent=1)+"\n")
    print("All four certified at 19 gates under every stated dominance constraint.")
