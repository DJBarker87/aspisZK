import NHT_Tx2AuthModel
import NHQ_RoundDomain
import NGS_PersistedCarriers
set_option autoImplicit false
noncomputable section
namespace NHT_AuthAccepted
open Aeneas Aeneas.Std Result VTop_Stages
/-- Actual driver acceptance supplies shape success and SAME common acceptance.
It does not supply an account index, data-read or persistence premise. -/
theorem common (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit))
 (accepted : NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs=ok (.Ok ())) :
 ∃ variant, ops.op3 proof=ok (.Ok variant) ∧
 NHT_EmittedCommon.tx2_common (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs=ok (.Ok ()) := by
 unfold NHT_EmittedAuth.tx2_authenticated at accepted
 obtain ⟨reply,shape,rest⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ accepted
 cases reply with
 | Err e => cases rest
 | Ok variant =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
   obtain ⟨_,mark,common⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ rest
   exact ⟨variant,shape,common⟩

/-- Reader-result transport only after the owning adapter installs this exact
fresh driver on the SAME pub/proof/checkpoint and literal release observer. -/
theorem reader_result (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (reader : Result (core.result.Result Unit verifier.Error))
 (stage2_owned : reader=NHT_EmittedAuth.tx2_authenticated
   (NHT_Tx2CommonModel.constants ops) D pub proof checkpoint hash none)
 (accepted : NHT_EmittedAuth.tx2_authenticated
   (NHT_Tx2CommonModel.constants ops) D pub proof checkpoint hash none=ok (.Ok ())) :
 reader=ok (.Ok ()) := stage2_owned.trans accepted
#print axioms common
#print axioms reader_result
#check AspisR1.NGS_CARRIERS.same_inputs_or_collision
#check AspisR1.NGR_HISTORY.saved_to_loaded
end NHT_AuthAccepted
