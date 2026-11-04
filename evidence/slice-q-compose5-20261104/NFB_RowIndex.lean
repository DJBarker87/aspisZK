import NFB_RowPrimitives
import NEB_GeometryIndices
set_option autoImplicit false
namespace NFB_RowIndex
open Aeneas Aeneas.Std Result

theorem indexPort (u : Usize) : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
    NEB_GeometryIndices.indexPort NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange u := by
 simp only [NFB_RowRef.aspis_core.r0.domain.FibreIndex.new,
   NFB_RowRef.aspis_core.r0.FIBRE_COUNT,bind_tc_ok,
   NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref]
 split <;> rfl

theorem admitted (u : Usize) (bound : u.val<262144) :
    NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=ok (.Ok u) := by
 rw [indexPort]
 exact NEB_GeometryIndices.admitted _ u bound

#print axioms indexPort
#print axioms admitted
end NFB_RowIndex
