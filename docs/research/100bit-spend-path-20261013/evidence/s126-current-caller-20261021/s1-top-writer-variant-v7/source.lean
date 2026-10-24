import S1TopPrepareSourceV1
import Port4A_PrepareCut
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result
open VTop_Stages
variable {CoreError W : Type}

/-- The exact lead writer-prefix consumer, with its prepareVariant premise
DISCHARGED for the complete source-body op7 installation. This does not claim
that remaining primitive/native-source and whole-Prepared bindings are closed. -/
theorem writer_variant (base : Ops) (sourceOps : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (batch : AspisR1.Port3_NativeBatchBody.Ops)
    (geometry : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
    (query : AspisR1.Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : AspisR1.VTop_Provenance.WriterPrefix
      (AspisR1.Port3_NativeWriterShape.installed (install base sourceOps) reserved batch geometry query finish)
      D hash semantic proof split none p a) : p.variant=.S2 := by
  apply AspisR1.Port4A_PrepareCut.variant_of_prepare (install base sourceOps) reserved batch geometry query finish
    D hash semantic proof split p a
  · intro zero g prepared source
    exact prepare_variant sourceOps D semantic proof hash (Array.repeat 29#usize zero) g prepared source
  · exact reached

#print axioms writer_variant
end AspisS1TopPrepareSource
