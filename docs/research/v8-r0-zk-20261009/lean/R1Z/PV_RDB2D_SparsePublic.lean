import R1Z.PV_RDB2D_SparseResource
namespace R1Z.PV_RDB2D_SparsePublic
open Aeneas Aeneas.Std Result PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape
set_option autoImplicit false

/-- This records the exact public-point transport still needed at the consuming
protocol call. It is not discharged merely by declaring point as an argument. -/
theorem point_transport {P H K : Type} (sourcePoint : P → H → List K) (publicPoint : P → List K)
    (public : ∀ p h, sourcePoint p h=publicPoint p) (isBoolean : K → Bool)
    (p : P) (left right : H) :
    publicRequest (PV_RDB2D_SparseLayout.request isBoolean (sourcePoint p left))=
      publicRequest (PV_RDB2D_SparseLayout.request isBoolean (sourcePoint p right)) := by rw [public,public]

theorem size_alignment_order {K H : Type} (isBoolean : K → Bool) (point : List K) (left right : H) :
    (fun (_ : H) => [publicRequest (PV_RDB2D_SparseLayout.request isBoolean point),
      .deallocate (24*capacity isBoolean point) 8]) left=
    (fun (_ : H) => [publicRequest (PV_RDB2D_SparseLayout.request isBoolean point),
      .deallocate (24*capacity isBoolean point) 8]) right := rfl

#print axioms point_transport
#print axioms size_alignment_order
end R1Z.PV_RDB2D_SparsePublic
