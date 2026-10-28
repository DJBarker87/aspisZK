import NDO_JHe_Natives
import NDO_JGx_RealStatement
import NDO_JFs_PublicValidation
import NDO_JHb_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkCodec
open Aeneas Aeneas.Std Result
abbrev statement := JGx_RealStatement.value
attribute [local irreducible] JHb_Header.value JFt_AfterstateValue.value

theorem decoded (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (JHe_Natives.sdk base stage).op47 JFx_NativeBytes.publicInput=ok (.Ok statement) :=
  JGx_RealStatement.decode
#print axioms decoded

theorem validated (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (JHe_Natives.sdk base stage).op21 statement=ok (.Ok ()) := by
  change JHe_SdkLeaves.validate statement=_
  unfold JHe_SdkLeaves.validate statement JGx_RealStatement.value
  rw [AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1,JFs_PublicValidation.source]
  rfl
#print axioms validated

theorem encoded (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (JHe_Natives.sdk base stage).op24 (S6N_Getters.commonValue statement).lane_transition.candidate_afterstate=
      ok (.Ok JHb_Header.value) := by
  obtain ⟨encoded,bytes,run⟩ := AspisS6NativeAfterstateCodec.accepted_inverse
    JHb_Header.value.to_slice JFt_AfterstateValue.value JHb_Header.candidate
  have same : encoded=JHb_Header.value := by
    apply Subtype.ext
    exact bytes
  subst encoded
  change JHe_SdkLeaves.afterstate _=_
  unfold JHe_SdkLeaves.afterstate
  change AspisS6OuterNativeOps.resultMap _
    (AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 JFt_AfterstateValue.value)=_
  rw [run]
  rfl
#print axioms encoded
end AspisR1.JHe_SdkCodec
end
