import R1Z.PV_CB3_WordMachine
import R1Z.PV_CB3_SamplerDivision
namespace R1Z.PV_CB3_MachinePass
open PV_CB3_SamplerWord PV_CB3_WordMachine
set_option autoImplicit false

/-- Typed high-to-low pass, stated recursively to expose the invariant before
any fixed eight-word expansion. -/
def passLE : List (BitVec 32) → List (BitVec 32) × BitVec 64
  | [] => ([], 0)
  | w :: ws =>
    let tail := passLE ws
    let head := step w tail.2
    (head.1 :: tail.1, head.2)

theorem remainder_canonical (words : List (BitVec 32)) :
    (passLE words).2.toNat < base := by
  induction words with
  | nil => change 0 < base; unfold base; omega
  | cons w ws ih => exact PV_CB3_WordMachine.remainder_canonical w (passLE ws).2 ih

theorem length_preserved (words : List (BitVec 32)) :
    (passLE words).1.length = words.length := by
  induction words with
  | nil => rfl
  | cons w ws ih => simp only [passLE, List.length_cons, ih]

/-- Every machine word, including both casts, refines the exact mathematical
long division. The canonical prior-remainder bound is derived internally. -/
theorem projection (words : List (BitVec 32)) :
    (passLE words).1.map BitVec.toNat =
      (PV_CB3_SamplerDivision.divideLE base radix (words.map BitVec.toNat)).1 ∧
    (passLE words).2.toNat =
      (PV_CB3_SamplerDivision.divideLE base radix (words.map BitVec.toNat)).2 := by
  induction words with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih =>
    have hc := remainder_canonical ws
    simp only [passLE, List.map_cons, PV_CB3_SamplerDivision.divideLE]
    rw [PV_CB3_WordMachine.quotient_value w _ hc,
      PV_CB3_WordMachine.remainder_value w _ hc, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

#print axioms remainder_canonical
#print axioms length_preserved
#print axioms projection
end R1Z.PV_CB3_MachinePass
