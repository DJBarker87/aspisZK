import NKQ_ArrayWindows
set_option autoImplicit false
namespace AspisR1.NKQ_MaskLowStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKQ_ArrayWindows
abbrev Q := aspis_core.field.QM31
abbrev Claims := Array (Array Q 29#usize) 3#usize

def lowAt (c : Claims) (i : Usize) (h : i.val<16) : Q :=
 cell (cell c 0 (by decide)) i.val (by omega)

theorem step {H : Type} (D : aspis_core.Digest32 H) (c : Claims)
 (i : Usize) (inside : i.val<16) :
 (FinishModel.closureFn9 D).call_mut c i=ok (lowAt c i inside,c) := by
 simp only [FinishModel.closureFn9,FinishModel.closureFn6]
 rw [read c 0#usize (by decide),bind_tc_ok]
 rw [read (cell c 0 (by decide)) i (by omega),bind_tc_ok]
 rfl

/-- The actual closure preserves the entire claims array, hence canonicality,
with no independently chosen post-state or child success premise. -/
theorem frame {H : Type} (D : aspis_core.Digest32 H) (c : Claims)
 (i : Usize) (inside : i.val<16) :
 ∃ value,(FinishModel.closureFn9 D).call_mut c i=ok (value,c) :=
 ⟨lowAt c i inside,step D c i inside⟩
#print axioms step
#print axioms frame
end AspisR1.NKQ_MaskLowStep
