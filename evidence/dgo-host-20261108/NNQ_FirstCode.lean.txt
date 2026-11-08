import NNQ_PreparePort
import NNQ_Batch
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem prepare_lower_eq {H : Type} (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D1 D2 : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (input : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkD_PrepareLower.lower (SdkD_PrepareSource.code base B std D1 pub proof hash input) =
    SdkD_PrepareLower.lower (SdkD_PrepareSource.code base B std D2 pub proof hash input) := by
  apply lowerP_dsim
  exact AspisR1CurrentCaller.S1PrepareCode.NNQ_Port.dictionary_irrelevant base
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B) D1 D2 pub proof hash input

theorem firstCode_eq {H : Type} (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 D2 : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (hash : H) :
    GExq_FirstCode.code base B std hv D1 pub publicBytes proof split hash =
    GExq_FirstCode.code base B std hv D2 pub publicBytes proof split hash := by
  simp only [GExq_FirstCode.code, prepare_lower_eq _ _ _ D1 D2, batch_eq D1 D2]

theorem secondCommon_eq {H : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 D2 : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub proof ck : Slice U8) (hash : H) :
    GExq_SecondCode.common base reserved hv D1 pub proof ck hash =
    GExq_SecondCode.common base reserved hv D2 pub proof ck hash := by
  simp only [GExq_SecondCode.common, batch_stage_eq D1 D2]

theorem secondCode_eq {H : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 D2 : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub proof ck : Slice U8) (hash : H) :
    GExq_SecondCode.code base reserved hv D1 pub proof ck hash =
    GExq_SecondCode.code base reserved hv D2 pub proof ck hash := by
  simp only [GExq_SecondCode.code, secondCommon_eq _ _ _ D1 D2]
#print axioms prepare_lower_eq
#print axioms firstCode_eq
#print axioms secondCommon_eq
#print axioms secondCode_eq
end AspisR1.NNQ_HostDigest
end
