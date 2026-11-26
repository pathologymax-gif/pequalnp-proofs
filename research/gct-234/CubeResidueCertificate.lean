import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Cubic discriminant obstruction at primes 11 and 13

Research contribution for PEqualNP gap L-gct-234, coordinated by Brett Snodgrass.
Each of the three support pairs gives the four exponent nodes of a cubed binomial.
If ten Euler moments vanish, applying the degree-eight nodal polynomial of the other
two cubes gives a residual cubic with a repeated nonzero root. Its discriminant
vanishes for each block. The finite theorems below certify the contrary whenever
at least eleven projected nodes are distinct modulo 11 or 13, after normalizing
one support pair to (0,1). Translating and scaling all exponents in the finite
field preserves distinctness and multiplies the discriminant by a nonzero power.
-/

namespace CubeResidueCertificate

def supportPairs (p : Nat) : List (Nat × Nat) :=
  (List.range p).flatMap fun a =>
    ((List.range p).filter fun b => a < b).map fun b => (a, b)

def nodes (p : Nat) (ab : Nat × Nat) : List Nat :=
  let (a, b) := ab
  [(3*a) % p, (2*a+b) % p, (a+2*b) % p, (3*b) % p]

def eligible (p : Nat) (u v : Nat × Nat) : Prop :=
  11 ≤ (nodes p (0,1) ++ nodes p u ++ nodes p v).eraseDups.length

instance (p : Nat) (u v : Nat × Nat) : Decidable (eligible p u v) := by
  unfold eligible
  infer_instance

def nodalValue (p : Nat) (others : List Nat) (z : Nat) : Int :=
  others.foldl (fun t x => (t * ((z : Int) - (x : Int))) % (p : Int)) 1

def disc (p : Nat) (ab u v : Nat × Nat) : Int :=
  let evalAt := nodalValue p (nodes p u ++ nodes p v)
  let (h,k) := ab
  let a := evalAt ((3*h)%p)
  let b := evalAt ((2*h+k)%p)
  let c := evalAt ((h+2*k)%p)
  let d := evalAt ((3*k)%p)
  ((b*c-a*d)^2 - 4*(b*b-a*c)*(c*c-b*d)) % (p : Int)

def excluded (p : Nat) (u v : Nat × Nat) : Prop :=
  disc p (0,1) u v ≠ 0 ∨ disc p u (0,1) v ≠ 0 ∨ disc p v (0,1) u ≠ 0

instance (p : Nat) (u v : Nat × Nat) : Decidable (excluded p u v) := by
  unfold excluded
  infer_instance

def verifies (p : Nat) : Bool :=
  (supportPairs p).all fun u => (supportPairs p).all fun v =>
    if eligible p u v then decide (excluded p u v) else true

theorem exclusion_of_check (p : Nat) (checked : verifies p = true)
    {u v : Nat × Nat} (hu : u ∈ supportPairs p) (hv : v ∈ supportPairs p)
    (he : eligible p u v) : excluded p u v := by
  have row := List.all_eq_true.mp checked u hu
  have cell := List.all_eq_true.mp row v hv
  exact of_decide_eq_true (by simpa [he] using cell)

set_option maxHeartbeats 0 in
theorem verifies_eleven : verifies 11 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem verifies_thirteen : verifies 13 = true := by decide +kernel

def offsetPair (p a d : Nat) : Nat × Nat := (a, (a+d) % p)

set_option maxHeartbeats 0 in
theorem gaps_one_two_four_mod_seventeen :
    ∀ a b : Fin 17, excluded 17 (offsetPair 17 a.val 2) (offsetPair 17 b.val 4) := by
  decide +kernel

#print axioms exclusion_of_check
#print axioms verifies_eleven
#print axioms verifies_thirteen
#print axioms gaps_one_two_four_mod_seventeen

end CubeResidueCertificate
