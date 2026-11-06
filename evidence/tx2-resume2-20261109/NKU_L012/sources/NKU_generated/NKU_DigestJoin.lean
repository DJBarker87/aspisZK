import NKU_DigestProof
import NKU_DigestPublic
import NKU_DigestCheckpoint
import NKK_HeaderSource
set_option autoImplicit false
noncomputable section
namespace NKU_DigestJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) («end» : Usize) : Stage Unit :=
 bind (NKU_DigestProof.run d hash) fun _=>
 bind (NKU_DigestPublic.run d hash) fun _=>NKU_DigestCheckpoint.run d hash «end»
/-- The three actual digest occurrences thread one parent state and feed
resumeBodyG. Model equality alone does not widen the native proof/public domains. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) (next : U8) («end» : Usize) :
 NKK_HeaderSource.afterHeader s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash next «end»=
 (do let reply ← run d hash «end» s
     NKK_Try.emitted reply (fun (_,post)=>resumeBodyG post.frame.reservation d post.frame.checkpoint .S2 next «end»)) := by
 unfold NKK_HeaderSource.afterHeader run NKU_Chronology.bind NKU_DigestProof.run NKU_DigestPublic.run NKU_DigestCheckpoint.run
 unfold NKK_DigestSource.model NKU_DigestCheckpoint.label
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NKK_Compare.ne_result,NKK_LogReduce.lift_ok_bind]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp_all only [decide_eq_true_eq,decide_eq_false_iff_not,not_not,ite_true,ite_false,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NKK_Compare.ne_result,NKK_LogReduce.lift_ok_bind])
#print source
#print axioms source
end NKU_DigestJoin
