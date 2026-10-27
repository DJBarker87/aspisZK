import LPo_B_LPa_Fold
set_option autoImplicit false
namespace LPo.BA

def firstBad (bad : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n+1 => match firstBad bad n with
    | some i => some i
    | none => if bad n then some n else none

theorem firstBad_find (bad : Nat → Bool) (n : Nat) :
    firstBad bad n = (List.range n).find? bad := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstBad, ih, List.range_succ, List.find?_append]
    cases h : (List.range n).find? bad <;> cases hb : bad n <;> simp [h, hb, List.find?]

theorem firstBad_fold (bad : Nat → Bool) (n : Nat) :
    firstBad bad n = (List.range n).foldl (fun found i =>
      match found with
      | some j => some j
      | none => if bad i then some i else none) none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstBad, ih, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

#print axioms firstBad_find
#print axioms firstBad_fold
end LPo.BA
