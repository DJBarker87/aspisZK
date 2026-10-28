import NBW_Conversions
set_option autoImplicit false
noncomputable section
namespace NBW_Dictionary
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
attribute [local instance] Classical.propDecidable
/-- Direct structural comparison. The native gate checks all eight limbs
and both equality branches; this definition alone gives no native credit. -/
def equality : core.cmp.PartialEq Stage2E Stage2E :=
 {eq:=fun x y=>ok (decide (x=y))}
def install (ops : Ops) : Ops :=
 {ops with
  op1:=fun q=>ok (NBF_RowInstall.embedQ q),
  op4:=ok 0#u32,op5:=ok 1#u32,
  op10:=fun m=>ok (NBF_RowInstall.embedM m),widePartialEq:=equality}
/-- Exact primitive dictionary entries; the remaining arithmetic and native
call-site installation are unchanged obligations. -/
theorem entries (ops : Ops) (q : NBF_RowInstall.Q) (m : U32) (x y : Stage2E) :
 (install ops).op1 q=ok (NBF_RowInstall.embedQ q) ∧
 (install ops).op4=ok 0#u32 ∧ (install ops).op5=ok 1#u32 ∧
 (install ops).op10 m=ok (NBF_RowInstall.embedM m) ∧
 (install ops).widePartialEq.eq x y=ok (decide (x=y)) :=
 ⟨rfl,rfl,rfl,rfl,rfl⟩
/-- The source != call uses the standard trait default on that same
comparison, preserving the complete Result. -/
theorem not_equal (x y : Stage2E) :
 core.cmp.PartialEq.ne.trait_default equality x y=ok (decide (x≠y)) := by
 by_cases h : x=y <;>
   simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,equality,h]
#print axioms entries
#print axioms not_equal
end NBW_Dictionary
end
