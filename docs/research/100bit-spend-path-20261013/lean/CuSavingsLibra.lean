import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-! Division-free tensor factorization for the retained S2 Libra row.
Reindexed a/b represent ap0[PERM[s]]/ap1[PERM[r]], and c is QUARTER.
The two 28-element runs cut the four 16-element blocks at 16+12 and 4+16+8.
This is algebra over arbitrary commutative semirings, so zero challenges are
included. Connecting these expressions to the emitted machine loops is separate.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsLibra
variable {R : Type} [CommSemiring R]

def lowRun (a : Nat → R) (c q : R) : R :=
  ((List.range 4).map (fun s => a s*c*q^s)).sum

def referenceBlock (a b : Nat → R) (c q : R) (start : Nat) (highs : List Nat) : R :=
  (highs.map (fun r => ((List.range 4).map
    (fun s => (a s*c)*(b r*c)*q^(start+4*r+s))).sum)).sum

theorem block_factor (a b : Nat → R) (c q : R) (start : Nat) (highs : List Nat) :
    referenceBlock a b c q start highs =
      lowRun a c q * (highs.map (fun r => b r*c*q^(4*r))).sum * q^start := by
  have inner (r : Nat) :
      ((List.range 4).map (fun s => (a s*c)*(b r*c)*q^(start+4*r+s))).sum =
        lowRun a c q * (b r*c*q^(4*r)) * q^start := by
    calc
      _ = ((List.range 4).map (fun s =>
          (a s*c*q^s)*((b r*c*q^(4*r))*q^start))).sum := by
        congr 1
        apply List.map_congr_left
        intro s _
        simp only [pow_add]
        ring
      _ = lowRun a c q * ((b r*c*q^(4*r))*q^start) :=
        List.sum_map_mul_right _ _ _
      _ = _ := (mul_assoc _ _ _).symm
  induction highs with
  | nil => simp only [referenceBlock,List.map_nil,List.sum_nil,mul_zero,zero_mul]
  | cons r rs ih =>
    change ((List.range 4).map (fun s => (a s*c)*(b r*c)*q^(start+4*r+s))).sum +
      referenceBlock a b c q start rs = _
    rw [inner,ih]
    simp only [List.map_cons,List.sum_cons]
    ring

def factoredWeights (a b : Nat → R) (c q0 q1 : R) : R × R × R × R :=
  let l0 := lowRun a c q0
  let l1 := lowRun a c q1
  let t (q : R) (r : Nat) := b r * c * q^(4*r)
  (l0 * (t q0 0 + t q0 1 + t q0 2 + t q0 3),
   l0 * (t q0 0 + t q0 1 + t q0 2) * q0^16 + l1 * (b 3*c),
   l1 * (t q1 0 + t q1 1 + t q1 2 + t q1 3) * q1^4,
   l1 * (t q1 0 + t q1 1) * (q1^16*q1^4))

/-- The shifted tail of block 1 starts at exponent zero in the SECOND run.
The row index is 3, but the exponent origin is 12. -/
def secondRunTail (a b : Nat → R) (c q : R) : R :=
  ((List.range 4).map (fun s => (a s*c)*(b 3*c)*q^s)).sum

theorem secondRunTail_factor (a b : Nat → R) (c q : R) :
    secondRunTail a b c q = lowRun a c q * (b 3*c) := by
  unfold secondRunTail lowRun
  calc
    _ = ((List.range 4).map (fun s => (a s*c*q^s)*(b 3*c))).sum := by
      congr 1
      apply List.map_congr_left
      intro s _
      ring
    _ = _ := List.sum_map_mul_right _ _ _

/-- Reference grouped by the actual 28=16+12 cut. The tail has a fresh
exponent origin, unlike a whole tensor block beginning at row zero. -/
def cutReferenceWeights (a b : Nat → R) (c q0 q1 : R) : R × R × R × R :=
  (referenceBlock a b c q0 0 [0,1,2,3],
   referenceBlock a b c q0 16 [0,1,2] + secondRunTail a b c q1,
   referenceBlock a b c q1 4 [0,1,2,3],
   referenceBlock a b c q1 20 [0,1])

theorem factored_eq_cutReference (a b : Nat → R) (c q0 q1 : R) :
    factoredWeights a b c q0 q1 = cutReferenceWeights a b c q0 q1 := by
  unfold factoredWeights cutReferenceWeights
  simp only [block_factor,secondRunTail_factor,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,pow_zero,mul_one]
  have hpow : q1^20 = q1^16*q1^4 := by rw [show (20:Nat)=16+4 from rfl,pow_add]
  rw [hpow]
  congr 1 <;> ring

#print axioms block_factor
#print axioms secondRunTail_factor
#print axioms factored_eq_cutReference
end AspisR1.CuSavingsLibra
