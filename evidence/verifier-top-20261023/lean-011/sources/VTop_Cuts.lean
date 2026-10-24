import VTop_Entry

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Cuts
open Aeneas Aeneas.Std Result VTop_Stages

theorem writer_reached (ops : VTop_Stages.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ p a, ops.op8 D p a proof pub hash = ok saved := by
  unfold verifier.candidate.tx1 at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals trace_state
  all_goals first
  | exact ⟨_,_,by assumption⟩
  | aesop

theorem resume_reached (ops : VTop_Stages.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ p a, ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,a)) := by
  unfold verifier.candidate.tx2_authenticated verifier.candidate.tx2_common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals first
  | exact ⟨_,_,by assumption⟩
  | aesop

#print axioms writer_reached
#print axioms resume_reached
end AspisR1.VTop_Cuts
end
