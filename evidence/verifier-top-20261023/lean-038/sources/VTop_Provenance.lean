import VTop_Entry

/-! Successful preparation/query/flush cuts only. This predicate contains no
checkpoint result, encoding, header or whole-caller acceptance conclusion. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Provenance
open Aeneas Aeneas.Std Result VTop_Stages

def WriterPrefix (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) : Prop :=
  ∃ zero g initial root geometry pending queried pendingAfter flushed,
    ops.op7 D semantic proof hash obs (Array.repeat 29#usize zero) = ok (.Ok p,g) ∧
    ops.op12 .S2 = ok (.Ok initial) ∧
    ops.op5 D proof p root 0#usize hash = ok (.Ok ()) ∧
    ops.op11 p.queries 0#usize split = ok (.Ok geometry) ∧
    ops.op10 initial.weights.deref = ok (.Ok pending) ∧
    ops.op6 proof p initial g obs geometry pending split = ok (.Ok (queried,pendingAfter)) ∧
    ops.op9 pendingAfter queried.weights.deref = ok flushed ∧
    a.weights.val = flushed.val ∧ a.rhs = queried.rhs ∧ a.power = queried.power ∧ a.next = queried.next

theorem writer_prefix (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ p a, WriterPrefix ops D hash semantic proof split obs p a ∧
      ops.op8 D p a proof pub hash = ok saved := by
  unfold verifier.candidate.tx1 at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    rw [← same]
    refine ⟨_,_,?_,by assumption⟩
    unfold WriterPrefix
    all_goals aesop

#print axioms writer_prefix
end AspisR1.VTop_Provenance
end
