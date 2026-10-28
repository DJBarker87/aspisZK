import NDO_JGx_Common
import NDO_JGx_Shape
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Authenticated
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
attribute [local irreducible] VTop_Stages.verifier.candidate.tx2_common

theorem source {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    VTop_Stages.verifier.candidate.tx2_authenticated (JGx_StageDictionary.source base seed err geometry query)
      (JFn_HashBoundary.dictionary JFp_SHADigest.digest D) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof JFx_NativeBytes.checkpoint hash none=ok (.Ok ()) := by
  unfold VTop_Stages.verifier.candidate.tx2_authenticated
  have shape : (JGx_StageDictionary.source base seed err geometry query).op3 JFx_NativeBytes.proof=ok (.Ok .S2) := JGx_Shape.source
  rw [shape,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  change VTop_Stages.verifier.candidate.tx2_common _ _ _ _ _ _ none=ok (.Ok ())
  exact JGx_Common.source base seed err geometry query D hash realizes
#print axioms source
end AspisR1.JGx_Authenticated
end
