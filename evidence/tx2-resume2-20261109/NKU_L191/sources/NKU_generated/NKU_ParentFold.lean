import NKU_FineHeader
import NKU_FineRoot
set_option autoImplicit false
noncomputable section
namespace NKU_ParentFold
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
/-- Complete G: iterator, every raw/E/K occurrence and owned allocation all
belong to one parent State. No source suffix or free callee clause remains. -/
def G {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineHeader.run d s
 NKK_Try.emitted reply (fun (_,post)=>NKU_Fold.suffix d hash post)
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 G d hash s=NKU_Fold.G d hash s := by
 unfold G NKU_Fold.G
 rw [NKU_FineHeader.installed]
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 G d hash s=NJU_ResumeObserved.run s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash :=
 (installed d hash s).trans (NKU_FineRoot.source d hash s)
theorem cohort {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NIL_StatePort.reply (G d hash s).result=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved s.frame.reservation))
 d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash := by
 rw [installed]
 exact NKU_FineRoot.cohort d hash s
theorem clauses {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause s.frame.reservation d hash) (G d hash s) := by
 rw [installed,NKU_FineRoot.installed]
 exact NKU_ResumeRoot.clauses d hash s
#print G
#print source
#print cohort
#print clauses
#print axioms installed
#print axioms source
#print axioms cohort
#print axioms clauses
end NKU_ParentFold
