import NHT_PacketOps
import NHQ_QueryFrame
set_option autoImplicit false
noncomputable section
namespace NHT_CommonCuts
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
/-- Resume is replaced at its actual child cut by a named full-Result packet.
Nothing asserts resume success, acceptance, or a chosen final driver output. -/
theorem resume (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit))
 (packet : Result (R (verifier.Prepared × verifier.Accumulator)))
 (NFU_resume : ops.op18 D checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash=packet) :
 NHT_EmittedCommon.tx2_common (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs =
 (do let reply ← packet
     NHQ_Tx2CommonModel.afterResume (NHT_Tx2CommonModel.constants ops) D proof hash obs reply) := by
 rw [NHT_Tx2CommonModel.retained_stages]
 unfold NHQ_Tx2CommonModel.run
 change (do let reply ← ops.op18 D checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash
            NHQ_Tx2CommonModel.afterResume (NHT_Tx2CommonModel.constants ops) D proof hash obs reply)=_
 rw [NFU_resume]

theorem resume_error (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (e : verifier.Error)
 (NFU_resume : ops.op18 D checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash=ok (.Err e)) :
 NHT_EmittedCommon.tx2_common (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs=ok (.Err e) := by
 rw [resume ops D pub proof checkpoint hash obs _ NFU_resume]
 rfl

theorem resume_fail (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (e : Aeneas.Std.Error)
 (NFU_resume : ops.op18 D checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash=.fail e) :
 NHT_EmittedCommon.tx2_common (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs=.fail e := by
 rw [resume ops D pub proof checkpoint hash obs _ NFU_resume]
 rfl

theorem resume_div (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit))
 (NFU_resume : ops.op18 D checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash=.div) :
 NHT_EmittedCommon.tx2_common (NHT_Tx2CommonModel.constants ops)
   D pub proof checkpoint hash obs=.div := by
 rw [resume ops D pub proof checkpoint hash obs _ NFU_resume]
 rfl
#print axioms resume
#print axioms resume_error
#print axioms resume_fail
#print axioms resume_div
end NHT_CommonCuts
