import RPz7_F3R_PairModelFinish
set_option autoImplicit false
namespace AspisR1.F3R_PreparationInstall
open Aeneas Aeneas.Std

theorem code {C Hash : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (input : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkD_PrepareSource.code
      (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base (Op5T_Concrete.current ops) reserved query geo)))
      B std D pub proof hash input=
    SdkD_PrepareSource.code (Uni_Install.current ops reserved query geo) B std D pub proof hash input := by
  rfl

#print axioms code
end AspisR1.F3R_PreparationInstall
