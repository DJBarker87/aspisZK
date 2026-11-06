import Aeneas
set_option autoImplicit false
noncomputable section
namespace NJI_Array64
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

/-- Generic extension of the existing byte law; required for the master's eight
U64 sequence words. No concrete word enumeration or whole-buffer reduction. -/
theorem lists {T : Type} [DecidableEq T] (cmp : core.cmp.PartialEq T T)
 (law : ∀ x y, cmp.ne x y=ok (decide (x≠y)))
 (xs ys : List T) (width : xs.length=ys.length) :
 List.allM (fun (x,y) => do let b ← cmp.ne x y;ok (¬ b)) (xs.zip ys)=
 ok (decide (xs=ys)) := by
 induction xs generalizing ys with
 | nil =>
  cases ys with
  | nil => rfl
  | cons y ys => simp at width
 | cons x xs ih =>
  cases ys with
  | nil => simp at width
  | cons y ys =>
   have tail := Nat.succ.inj width
   by_cases same : x=y
   · subst y
     simpa [List.allM,law] using ih ys tail
   · simp [List.allM,law,same]
     rfl

theorem scalar (x y : U64) : core.cmp.PartialEqU64.ne x y=ok (decide (x≠y)) := by
 by_cases h : x=y <;> simp [core.cmp.PartialEqU64,core.cmp.impls.PartialEqU64.ne,h]

theorem eq_value {N : Usize} (a b : Array U64 N) :
 core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b=ok (decide (a=b)) := by
 have width : a.val.length=b.val.length := a.property.trans b.property.symm
 unfold core.array.equality.PartialEqArray.eq
 simp only [show a.length=b.length from width,if_true]
 change List.allM (fun (x,y) => core.cmp.PartialEqU64.ne x y >>= fun different => ok (¬ different))
  (a.val.zip b.val)=ok (decide (a=b))
 have eqv : a=b ↔ a.val=b.val := Subtype.ext_iff
 have decisions : decide (a.val=b.val)=decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,←eqv]
 rw [←decisions]
 exact lists core.cmp.PartialEqU64 scalar a.val b.val width

theorem ne_value {N : Usize} (a b : Array U64 N) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU64 a b=ok (decide (a≠b)) := by
 rw [core.array.equality.PartialEqArray.ne,eq_value]
 by_cases h : a=b <;> simp [h]

#print axioms lists
#print axioms scalar
#print axioms eq_value
#print axioms ne_value
end NJI_Array64
