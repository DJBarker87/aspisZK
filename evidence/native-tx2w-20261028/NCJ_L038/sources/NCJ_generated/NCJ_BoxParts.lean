import FIn_WeightsFuns
set_option autoImplicit false
namespace NCJ_BoxParts
open Aeneas Aeneas.Std Result FIn_WeightsExtract

theorem source (variant : FInVariant)
    (factors : Array (Array (Array field.QM31 4#usize) 5#usize) 5#usize)
    (points : Array (Array field.QM31 10#usize) 3#usize)
    (extra : Array field.QM31 2#usize) :
    ∃ w,Weights.box_from_parts variant factors points extra=ok w ∧
      w.variant=variant ∧ w.factors=factors ∧ w.points=points ∧ w.extra=extra :=
  ⟨⟨variant,factors,points,extra⟩,rfl,rfl,rfl,rfl,rfl⟩

/-- Pointwise native windows compose to complete SAME record identity. This
is extensional composition; actual allocation/ownership remains the runtime
and source caller obligation, not an assumed equality of allocation addresses. -/
theorem record_eq (a b : Weights) (variant : a.variant=b.variant)
    (factors : a.factors=b.factors) (points : a.points=b.points) (extra : a.extra=b.extra) : a=b := by
  cases a
  cases b
  simp_all

#print axioms source
#print axioms record_eq
end NCJ_BoxParts
