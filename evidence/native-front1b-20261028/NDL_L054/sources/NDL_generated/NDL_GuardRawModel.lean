import NDL_GuardRef.Funs
import NCJ_GuardExact
import LPf_ArrayFour
set_option autoImplicit false
noncomputable section
namespace NDL_GuardRawModel
open Aeneas Aeneas.Std Result FIo_Native
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31
abbrev Row := Array Q 4#usize

def qArray (x : Q) : Array U32 4#usize := Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
def rowArray (x : Row) : Array (Array U32 4#usize) 4#usize :=
  Array.make 4#usize [qArray (NCJ_GuardExact.pick x 0 (by decide)),
    qArray (NCJ_GuardExact.pick x 1 (by decide)),
    qArray (NCJ_GuardExact.pick x 2 (by decide)),
    qArray (NCJ_GuardExact.pick x 3 (by decide))]
def variant : transport.Variant → U8 | .S1=>0#u8 | .S2=>1#u8 | .D=>2#u8

theorem qeq (x y : Q) :
    NDL_GuardRef.qeq_ref (qArray x) (qArray y)=ok (decide (x=y)) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  simp [NDL_GuardRef.qeq_ref,qArray,Array.index_usize,Array.make]
  repeat' split <;> simp_all

theorem roweq (x y : Row) :
    NDL_GuardRef.roweq_ref (rowArray x) (rowArray y)=ok (decide (x=y)) := by
  obtain ⟨a,b,c,d,hx⟩ := AspisR1.LPf_ArrayFour.shape x
  obtain ⟨e,f,g,h,hy⟩ := AspisR1.LPf_ArrayFour.shape y
  subst x;subst y
  simp [NDL_GuardRef.roweq_ref,rowArray,NCJ_GuardExact.pick,
    Array.index_usize,Array.make,qeq]
  repeat' split <;> simp_all

/-- Complete safe raw-word reference versus the adopted guard. Native K032
checks the ACTUAL function against this reference, not comparison Bool cuts. -/
theorem cohort (w : weights.Weights) (folds : Usize) :
    NDL_GuardRef.guard_raw_ref (variant w.variant) folds
      (rowArray (NCJ_GuardExact.row w 0 2)) (rowArray (NCJ_GuardExact.row w 2 2))
      (rowArray (NCJ_GuardExact.row w 0 3)) (rowArray (NCJ_GuardExact.row w 2 3)) =
      weights.shared_two_point_guard w folds := by
  rw [NCJ_GuardExact.source]
  cases hv : w.variant <;>
    simp [NDL_GuardRef.guard_raw_ref,variant,roweq,NCJ_GuardExact.guard,hv]
  repeat' split <;> simp_all

#print axioms qeq
#print axioms roweq
#print axioms cohort
end NDL_GuardRawModel
end
