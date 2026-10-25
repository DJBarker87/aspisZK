import Port3_Parents
import VTop_Cuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Cuts
open Aeneas Aeneas.Std Result VTop_Stages

/-- The physical batch0 cut is obtained from this accepted TX1, not from
another existentially chosen successful batch. -/
theorem tx1_batch (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ p root, ops.op5 D proof p root 0#usize hash = ok (.Ok ()) := by
  obtain ⟨p,a,reached,writer⟩ := VTop_Provenance.writer_prefix ops D hash semantic pub proof split obs saved accepted
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,rest⟩ := reached
  exact ⟨p,root,hbatch⟩

/-- The physical batch1 Prepared is exactly the one returned by this SAME
TX2 resume on the fixed checkpoint/proof/public slices. -/
theorem tx2_batch (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ p a root,
      ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,a)) ∧
      ops.op5 D proof p root 1#usize hash = ok (.Ok ()) := by
  unfold verifier.candidate.tx2_authenticated verifier.candidate.tx2_common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,by assumption,by assumption⟩

#print axioms tx1_batch
#print axioms tx2_batch
end AspisR1.Port4B_Cuts
end
