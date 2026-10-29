import R1Z.PV_RDCD3_RangeFold

namespace R1Z.PV_RDCD3_OrderedFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDCD3_RangeFold

/-- A list of exactly the callback arguments, in source iteration order. -/
def indices : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,start => start :: indices n (start+1)

def fold {S : Type} (f : S → Nat → Result S) : List Nat → S → Result S
  | [],acc => ok acc
  | x::xs,acc => do let acc' ← f acc x; fold f xs acc'

theorem ordered_indices {S : Type} (f : S → Nat → Result S)
    (n start : Nat) (acc : S) :
    ordered f n start acc = fold f (indices n start) acc := by
  induction n generalizing start acc with
  | zero => rfl
  | succ n ih =>
    simp only [ordered,indices,fold]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro acc' _
    exact ih (start+1) acc'

theorem append {S : Type} (f : S → Nat → Result S)
    (xs ys : List Nat) (acc : S) :
    fold f (xs++ys) acc = (do let middle ← fold f xs acc; fold f ys middle) := by
  induction xs generalizing acc with
  | nil => simp only [List.nil_append,fold,bind_tc_ok]
  | cons x xs ih =>
    simp only [List.cons_append,fold,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro acc' _
    exact ih acc'

theorem list_foldlM {S : Type} (f : S → Nat → Result S)
    (xs : List Nat) (acc : S) :
    fold f xs acc = xs.foldlM f acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [fold,List.foldlM_cons]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro acc' _
    exact ih acc'

/-- Exact five-factor range used by Weights::raw tensor branch. -/
theorem five {S : Type} (f : S → Nat → Result S) (acc : S) :
    ordered f 5 0 acc = [0,1,2,3,4].foldlM f acc := by
  rw [ordered_indices,list_foldlM]
  rfl

/-- Exact ten-coordinate range used by Weights::raw point branch. -/
theorem ten {S : Type} (f : S → Nat → Result S) (acc : S) :
    ordered f 10 0 acc = [0,1,2,3,4,5,6,7,8,9].foldlM f acc := by
  rw [ordered_indices,list_foldlM]
  rfl

#print axioms ordered_indices
#print axioms append
#print axioms list_foldlM
#print axioms five
#print axioms ten
end R1Z.PV_RDCD3_OrderedFold
