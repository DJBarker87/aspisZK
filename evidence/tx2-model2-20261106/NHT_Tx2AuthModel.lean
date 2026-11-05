import NHT_EmittedAuth
import NHT_Tx2CommonModel
import NHQ_Tx2AuthModel
set_option autoImplicit false
noncomputable section
namespace NHT_Tx2AuthModel
open Aeneas Aeneas.Std Result VTop_Stages
/-- Authenticated driver now actually delegates to the fresh common control body. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants ops)
  D pub proof checkpoint hash obs =
 verifier.candidate.tx2_authenticated (NHT_Tx2CommonModel.constants ops)
  D pub proof checkpoint hash obs := by
 unfold NHT_EmittedAuth.tx2_authenticated verifier.candidate.tx2_authenticated
 rw [NHT_Tx2CommonModel.source]
 rfl

theorem retained_stages (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants ops)
  D pub proof checkpoint hash obs =
 NHQ_Tx2AuthModel.run (NHT_Tx2CommonModel.constants ops)
  D pub proof checkpoint hash obs :=
 (source ops D pub proof checkpoint hash obs).trans
  (NHQ_Tx2AuthModel.source (NHT_Tx2CommonModel.constants ops)
    D pub proof checkpoint hash obs)
#print axioms source
#print axioms retained_stages
end NHT_Tx2AuthModel
