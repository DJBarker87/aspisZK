import NDO_JHi_AfterstateDecoderAction
import NDO_JHi_RawValuesValidated
import JHi_RetypeSuccess
import RPz7_S2K_AfterstateEncoding
set_option autoImplicit false
namespace AspisR1.JHi_AfterstateAccepted
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem source : ∃ encoded : Array U8 688#usize,
    aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      JHg_RawCommon.common.lane_transition.candidate_afterstate=ok (.Ok encoded) := by
  have run:=S2K.AfterstateEncoding.encode_exact JFt_AfterstateValue.value JFt_AfterstateValue.validated
  rw [JHi_AfterstateDecoderAction.source _ JFt_AfterstateValue.validated] at run
  have raw:=JHi_AfterstateBody.source _ JHi_RawValuesValidated.afterstate
  have same : JHi_AfterstateBody.decode JHg_RawCommon.common.lane_transition.candidate_afterstate=
      JFt_AfterstateValue.value := rfl
  rw [same] at raw
  exact ⟨_,raw.trans (JHi_RetypeSuccess.source _ _ run)⟩
#print axioms source
end AspisR1.JHi_AfterstateAccepted
