import NBG_Utilities
set_option autoImplicit false
noncomputable section
namespace NGL_ArrayEquality
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem eq_value {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b =
      ok (decide (a = b)) := by
  have width : a.val.length = b.val.length := a.property.trans b.property.symm
  unfold core.array.equality.PartialEqArray.eq
  simp only [show a.length = b.length from width, if_true]
  change List.allM (fun (x,y) => core.cmp.PartialEqU8.ne x y >>=
    fun different => ok (¬ different)) (a.val.zip b.val) = ok (decide (a = b))
  have value_iff : a = b ↔ a.val = b.val := by
    constructor
    · intro same
      exact congrArg (fun x : Array U8 N => x.val) same
    · intro same
      cases a
      cases b
      cases same
      rfl
  have decisions : decide (a.val = b.val) = decide (a = b) := by
    by_cases same : a = b
    · subst b
      simp
    · have different : a.val ≠ b.val := fun h => same (value_iff.mpr h)
      simp only [same,different,decide_false]
  rw [← decisions]
  exact NBG_Utilities.lists a.val b.val width

theorem ne_value {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b =
      ok (!(decide (a = b))) := by
  rw [core.array.equality.PartialEqArray.ne,eq_value]
  simp only [bind_tc_ok]
  cases decide (a = b) <;> rfl
#print axioms eq_value
#print axioms ne_value
end NGL_ArrayEquality
