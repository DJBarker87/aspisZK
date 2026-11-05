import NGM_GuardRef.Funs
import NGM_GuardExact
import NGM_ArrayFour
set_option autoImplicit false
noncomputable section
namespace NGM_GuardRawModel
open Aeneas Aeneas.Std Result FIo_Native
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31
abbrev Row := Array Q 4#usize

def qArray (x : Q) : Array U32 4#usize := Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
def rowArray (x : Row) : Array (Array U32 4#usize) 4#usize :=
  Array.make 4#usize [qArray (NGM_GuardExact.pick x 0 (by decide)),
    qArray (NGM_GuardExact.pick x 1 (by decide)),
    qArray (NGM_GuardExact.pick x 2 (by decide)),
    qArray (NGM_GuardExact.pick x 3 (by decide))]
def variant : transport.Variant → U8 | .S1=>0#u8 | .S2=>1#u8 | .D=>2#u8

theorem qeq (x y : Q) :
    NGM_GuardRef.qeq_ref (qArray x) (qArray y)=ok (decide (x=y)) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  simp [NGM_GuardRef.qeq_ref,qArray,Array.index_usize,Array.make]
  repeat' split <;> simp_all

theorem make_eq (a b c d e f g h : Q) :
    (Array.make 4#usize [a,b,c,d] = Array.make 4#usize [e,f,g,h]) ↔
      a=e ∧ b=f ∧ c=g ∧ d=h := by
  constructor
  · intro same
    have values := congrArg (fun z : Row=>z.val) same
    change [a,b,c,d]=[e,f,g,h] at values
    simpa only [List.cons.injEq,eq_self_iff_true,and_true] using values
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

theorem roweq (x y : Row) :
    NGM_GuardRef.roweq_ref (rowArray x) (rowArray y)=ok (decide (x=y)) := by
  obtain ⟨a,b,c,d,hx⟩ := AspisR1.NGM_ArrayFour.shape x
  obtain ⟨e,f,g,h,hy⟩ := AspisR1.NGM_ArrayFour.shape y
  subst x;subst y
  rw [make_eq]
  simp [NGM_GuardRef.roweq_ref,rowArray,NGM_GuardExact.pick,
    Array.index_usize,Array.make,Subtype.mk.injEq,List.cons.injEq,qeq]
  repeat' split <;> simp_all [Subtype.mk.injEq,List.cons.injEq]

/-- Complete safe raw-word reference versus the adopted guard. Native K032
checks the ACTUAL function against this reference, not comparison Bool cuts. -/
theorem cohort (w : weights.Weights) (folds : Usize) :
    NGM_GuardRef.guard_raw_ref (variant w.variant) folds
      (rowArray (NGM_GuardExact.row w 0 2)) (rowArray (NGM_GuardExact.row w 2 2))
      (rowArray (NGM_GuardExact.row w 0 3)) (rowArray (NGM_GuardExact.row w 2 3)) =
      weights.shared_two_point_guard w folds := by
  rw [NGM_GuardExact.source]
  cases hv : w.variant <;>
    simp [NGM_GuardRef.guard_raw_ref,variant,roweq,NGM_GuardExact.guard,hv]
  repeat' split <;> simp_all

#print axioms qeq
#print axioms make_eq
#print axioms roweq
#print axioms cohort
end NGM_GuardRawModel
end
