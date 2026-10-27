import XRr_Candidate64
import XRr_FinishLength
import XRr_VecRestoration
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_Materialized64
/-- SAME candidate, finish and library restoration yield the actual final
64-weight checkpoint carrier; no second successful query/finish is assumed. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok saved)) :
 split=compact.SPLIT ∧ ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
 a.weights.val.length=64 ∧ a.next.val=split.val ∧
 verifier.checkpoint D p a proof physical hash=ok saved := by
 obtain ⟨splitEq,p,a,pending,slice,restore,finished,length,next,hrestore,hfinish,hcheckpoint⟩ :=
   XRr_Candidate64.source D pub physical proof split hash obs saved run
 have restored := XRr_VecRestoration.source a.weights slice restore hrestore
 have finishedLength := XRr_FinishLength.source pending slice finished hfinish
 refine ⟨splitEq,p,{a with weights:=restore finished},?_,next,hcheckpoint⟩
 have hlist := restored.2 finished
 change (restore finished).val.length=64
 rw [hlist,finishedLength]
 change slice.val.length=64
 rw [restored.1,length]
#print axioms source
end XRr_Materialized64
