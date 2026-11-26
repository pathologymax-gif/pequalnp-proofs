import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19109

open PEqualNP.CircuitLowerBounds

private def witness : Circuit where
  gates := [
      ⟨.and, [0, 4]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.or, [2, 10]⟩,
      ⟨.or, [1, 11]⟩,
      ⟨.and, [9, 12]⟩,
      ⟨.or, [8, 13]⟩,
      ⟨.not, [14]⟩]
  output := 15

end PEqualNP.Outside.L_meta_19109

theorem PEqualNP.Outside.L_meta_19109 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 4 => (15838 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19109.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19109.witness,
    Set.mem_insert_iff, Set.mem_singleton_iff]
