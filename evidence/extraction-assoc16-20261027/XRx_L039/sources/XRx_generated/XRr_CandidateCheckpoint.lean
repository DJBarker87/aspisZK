import XRr_Materialized64
import XRr_CheckpointAttempts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_CandidateCheckpoint
/-- Full model checkpoint cut shares the exact physically supplied proof/public
bytes and the source's final materialized accumulator. No opaque leaf is filled. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok saved)) :
 split=compact.SPLIT ∧ ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
 (proofHash publicHash : Array U8 32#usize) (payload : Slice U8) (checksum : Array U8 32#usize),
 a.weights.val.length=64 ∧ a.next.val=split.val ∧
 verifier.checkpoint D p a proof physical hash=ok saved ∧
 XRn_Join_digest D hash [proof]=ok proofHash ∧
 XRn_Join_digest D hash [physical]=ok publicHash ∧
 XRn_Join_digest D hash [XRr_CheckpointAttempts.label,payload]=ok checksum ∧
 saved.val=payload.val++checksum.val ∧
 saved.val.length=(if p.variant matches .S1 then 4840 else 1768) := by
 obtain ⟨splitEq,p,a,length,next,hcheckpoint⟩ :=
   XRr_Materialized64.source D pub physical proof split hash obs saved run
 obtain ⟨ph,puh,payload,checksum,hph,hpuh,hchecksum,bytes⟩ :=
   XRr_CheckpointAttempts.source D p a proof physical hash saved hcheckpoint
 exact ⟨splitEq,p,a,ph,puh,payload,checksum,length,next,hcheckpoint,hph,hpuh,hchecksum,bytes,
   XRr_CheckpointShape.size D p a proof physical hash saved hcheckpoint⟩
#print axioms source
end XRr_CandidateCheckpoint
