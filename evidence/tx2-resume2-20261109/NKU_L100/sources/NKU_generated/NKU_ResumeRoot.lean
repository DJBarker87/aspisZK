import NKU_HeaderStep
import NKU_DigestBody
import NKK_ClauseRoot
set_option autoImplicit false
noncomputable section
namespace NKU_ResumeRoot
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Whole native parent G, expressed as a chronological state fold. Every
stage receives the preceding returned NKU.State; rejected/aborted prefixes
short-circuit before later stages. There is no source suffix left in G. -/
def suffix {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) :=
 match s.decoded.next,s.decoded.endAt with
 | some next,some «end» => NKU_DigestBody.run d hash s next «end»
 | _,_ => liftM (Result.fail .panic)
def G {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_HeaderStep.run d s
 NKK_Try.emitted reply (fun (_,post)=>suffix d hash post)
theorem suffix_eq {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) : NKU_HeaderStep.suffix d hash s=suffix d hash s := by
 unfold NKU_HeaderStep.suffix suffix
 cases s.decoded.next with
 | none => rfl
 | some next =>
  cases s.decoded.endAt with
  | none => rfl
  | some «end» => exact NKU_DigestBody.source d hash s next «end»
/-- Forward native-G/source association, full Result AND chronological events.
All child Results are instantiated internally at SAME arguments. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) :
 G d hash s=NJU_ResumeObserved.run s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash := by
 symm
 rw [NKU_HeaderStep.source]
 unfold G
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair => exact suffix_eq d hash pair.2
/-- The concrete child clauses are outputs of the parent theorem, never a
root hypothesis or a second independently selected successful invocation. -/
theorem clauses {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause s.frame.reservation d hash) (G d hash s) := by
 rw [source]
 exact (NKK_ClauseRoot.source s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash).1
/-- Adopted cohort transport of this SAME complete parent fold. -/
theorem cohort {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) :
 NIL_StatePort.reply (G d hash s).result=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved s.frame.reservation))
 d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash := by
 rw [source]
 exact NJU_ResumeRoot.cohort s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes hash
#print G
#print source
#print clauses
#print cohort
#print axioms suffix_eq
#print axioms source
#print axioms clauses
#print axioms cohort
end NKU_ResumeRoot
