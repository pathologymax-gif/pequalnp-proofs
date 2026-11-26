"""Generate independent Lean submissions from 4-by-4 one-hot circuit witnesses."""

import argparse
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def render(step, witness):
    mask, bound = witness["mask"], witness["bound"]
    gates, output = witness["gates"], witness["output"]
    if not str(step).isdigit() or not (0 <= mask < 65536 and len(gates) <= bound):
        raise ValueError(f"invalid identifier, mask, or size in {step}")
    operations = []
    wires = [15 << (4 * i) for i in range(4)] + [0x1111 << i for i in range(4)]
    for operation, left, right in gates:
        if operation not in {"and", "or", "not"} or not 0 <= left < len(wires):
            raise ValueError(f"invalid gate in {step}")
        if operation == "not":
            operands = f"[{left}]"
            word = 65535 ^ wires[left]
        else:
            if not 0 <= right < len(wires):
                raise ValueError(f"invalid second operand in {step}")
            operands = f"[{left}, {right}]"
            word = wires[left] & wires[right] if operation == "and" else wires[left] | wires[right]
        operations.append(f"⟨.{operation}, {operands}⟩")
        wires.append(word)
    if not 0 <= output < len(wires) or wires[output] != mask:
        raise ValueError(f"truth-table mismatch in {step}")
    rows = ",\n      ".join(operations)
    return f"""import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_{step}

open PEqualNP.CircuitLowerBounds

private def witness : Circuit where
  gates := [
      {rows}]
  output := {output}

end PEqualNP.Outside.L_meta_{step}

theorem PEqualNP.Outside.L_meta_{step} :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ {bound} ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 4 => ({mask} : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_{step}.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_{step}.witness,
    Set.mem_insert_iff, Set.mem_singleton_iff]
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witnesses", nargs="*", type=Path, default=[HERE / "formula_witnesses.json"])
    parser.add_argument("--out", type=Path, default=HERE)
    args = parser.parse_args()
    args.out.mkdir(exist_ok=True, parents=True)
    for path in args.witnesses:
        for step, witness in json.loads(path.read_text(encoding="utf-8")).items():
            (args.out / f"L_meta_{step}.lean").write_text(render(step, witness), encoding="utf-8")
            print(step, len(witness["gates"]), witness["mask"])


if __name__ == "__main__":
    main()
