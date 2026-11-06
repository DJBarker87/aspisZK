import NKE_ResumeEval6
import NJU_ResumeRoot
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeAssociation
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Concrete resume G, over the SAME source log and actual Reservation.
Every reply is installed at its own call arguments, including Err/abort. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H) :
 NKE_FreeReplay.G (NKE_ResumeProgram.run reservation d ck proof pub v hash)
  (NJU_ResumeObserved.run reservation d ck proof pub v hash).events=
 NKE_FreeReplay.State.done
  (NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash) [] := by
 have actual := NKE_FreeReplay.source (NKE_ResumeProgram.run reservation d ck proof pub v hash)
 rw [NKE_ResumeEval.run,NJU_ResumeRoot.source] at actual
 exact actual

theorem prefixes (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H) (n : Nat) :
 NKE_FreeReplay.advance n (NKE_ResumeProgram.run reservation d ck proof pub v hash)
  (NJU_ResumeObserved.run reservation d ck proof pub v hash).events=
 NKE_FreeReplay.sourcePrefix n (NKE_ResumeProgram.run reservation d ck proof pub v hash) := by
 have actual := NKE_FreeReplay.prefixes (NKE_ResumeProgram.run reservation d ck proof pub v hash) n
 rw [NKE_ResumeEval.run] at actual
 exact actual

/-- Install THAT nested resume in C01 of the actual common body. No second
reservation, success premise, endpoint seed or independently chosen log. -/
theorem at_common (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) :
 NHT_ResultPort.action (NIL_StatePort.reply
  (NKE_Free.eval (NKE_ResumeProgram.run reservation (NJC_ResumeCalls.digest d)
   ck proof pub .S2 hash)).result)=
 NJJ_Common.resume reservation d ck proof pub .S2 hash := by
 rw [NKE_ResumeEval.run,NJU_ResumeRoot.source]
 rfl
#print source
#print prefixes
#print at_common
#print axioms source
#print axioms prefixes
#print axioms at_common
end NKE_ResumeAssociation
