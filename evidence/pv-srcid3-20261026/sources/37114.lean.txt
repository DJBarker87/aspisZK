import R1Z.PV_Src_ReduceModulo
import R1Z.PV_Src_ExternalReference

/-! The same extracted scalar reducer in the admission source and owned
external callback has identical complete Result semantics for arbitrary U64. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortReduce
open Aeneas Aeneas.Std Result

theorem source (x : U64) :
    BuilderForestAdmissionPort.aspis_core.field.M31.reduce_u62 x =
      AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62 x := by
  simp only [BuilderForestAdmissionPort.aspis_core.field.M31.reduce_u62,
    BuilderForestAdmissionPort.aspis_core.field.reduce_u64,
    BuilderForestAdmissionPort.aspis_core.field.P,
    AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62,
    AspisBuilderPoseidonReference.aspis_core.field.reduce_u64,
    AspisBuilderPoseidonReference.aspis_core.field.P,lift,bind_tc_ok]

theorem modulo (x : U64) :
    BuilderForestAdmissionPort.aspis_core.field.M31.reduce_u62 x =
      (do let r ← x % (UScalar.cast .U64 R0PoseidonCopy.P)
          ok (UScalar.cast .U32 r)) := by
  rw [source,PV_Src_ReduceModulo.reference]

#print axioms source
#print axioms modulo
end R1Z.PV_Src_PortReduce
