import NFB_RowRef.Funs
import NFB_MulDischarge
set_option autoImplicit false
namespace NFB_RowPrimitives
open Aeneas Aeneas.Std Result
namespace N
abbrev F := NFB_RowRef.aspis_core.field.M31
end N

theorem double (x : U32) : NFB_RowRef.aspis_core.field.M31.double x=
    NEW_GeometryActual.aspis_core.field.M31.double x := by
 simp only [NFB_RowRef.aspis_core.field.M31.double,
   NEW_GeometryActual.aspis_core.field.M31.double,
   NFB_RowRef.aspis_core.field.M31.add,
   NEW_GeometryActual.aspis_core.field.M31.add,
   NFB_RowRef.aspis_core.field.P,NEW_GeometryActual.aspis_core.field.P]

theorem subtract (x y : U32) : NFB_RowRef.aspis_core.field.M31.sub x y=
    NEW_GeometryActual.aspis_core.field.M31.sub x y := by
 simp only [NFB_RowRef.aspis_core.field.M31.sub,
   NEW_GeometryActual.aspis_core.field.M31.sub,
   NFB_RowRef.aspis_core.field.P,NEW_GeometryActual.aspis_core.field.P]

theorem index (u : Usize) : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
    if u<262144#usize then ok (.Ok u)
    else ok (.Err NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange) := by rfl

theorem clone (word : U32) :
    NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone.clone word=ok word := by rfl

#print axioms double
#print axioms subtract
#print axioms index
#print axioms clone
end NFB_RowPrimitives
