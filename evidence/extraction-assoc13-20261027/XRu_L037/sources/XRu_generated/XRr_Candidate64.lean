import XRr_CandidateCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_Candidate64
/-- The checkpoint cut shares the accumulator whose length and query ordinal
are derived from the actual earlier initialization/query execution. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok saved)) :
 split=compact.SPLIT ∧ ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
   (pending : verifier.BatchedWeights) (slice : Slice aspis_core.field.QM31)
   (restore : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
   (finished : Slice aspis_core.field.QM31),
 a.weights.val.length=64 ∧ a.next.val=split.val ∧
 lift (alloc.vec.Vec.deref_mut a.weights)=ok (slice,restore) ∧
 verifier.BatchedWeights.finish pending slice=ok finished ∧
 verifier.checkpoint D p {a with weights:=restore finished} proof physical hash=ok saved := by
 obtain ⟨splitEq,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
   hshape,hscan,hzero,hprepare,hinit,hbatch,hgeo,hpending,hquery,hrestore,hfinish,hcheckpoint⟩ :=
   XRr_CandidateCuts.source D pub physical proof split hash obs saved run
 obtain ⟨calls,weights,length,next⟩ :=
   XRr_Accepted64.source proof p g obs geo split initial a pending0 pending hinit hquery
 exact ⟨splitEq,p,a,pending,slice,restore,finished,length,next,hrestore,hfinish,hcheckpoint⟩
#print axioms source
end XRr_Candidate64
