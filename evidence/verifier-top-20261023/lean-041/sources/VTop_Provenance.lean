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
  ∃ zero g preparation initial root geometry pending returned flushed parsed splitValue,
    ops.op16 = ok splitValue ∧ split.val = splitValue.val ∧
    ops.op3 proof = ok (.Ok parsed) ∧ ops.op4 proof = ok (.Ok ()) ∧ ops.op1 = ok zero ∧
    ops.op7 D semantic proof hash obs (Array.repeat 29#usize zero) = ok (preparation,g) ∧
    core.result.Result.Insts.CoreOpsTry.branch preparation = ok (.Continue p) ∧
    ops.op12 .S2 = ok (.Ok initial) ∧
    ops.op5 D proof p root 0#usize hash = ok (.Ok ()) ∧
    ops.op11 p.queries 0#usize split = ok (.Ok geometry) ∧
    ops.op10 initial.weights.deref = ok (.Ok pending) ∧
    ops.op6 proof p initial g obs geometry pending split = ok (.Ok returned) ∧
    ops.op9 returned.2 returned.1.weights.deref = ok flushed ∧
    a.weights.val = flushed.val ∧ a.rhs = returned.1.rhs ∧ a.power = returned.1.power ∧ a.next = returned.1.next

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
    match goal with
    | hz : ops.op1 = ok ?zero,
      hp : ops.op7 D semantic proof hash obs _ = ok ?prepared,
      hi : ops.op12 _ = ok (.Ok ?initial),
      hb : ops.op5 D proof _ ?root _ hash = ok (.Ok _),
      hg : ops.op11 _ _ split = ok (.Ok ?geometry),
      hn : ops.op10 _ = ok (.Ok ?pending),
      hq : ops.op6 proof _ _ _ obs _ _ split = ok (.Ok ?returned),
      hf : ops.op9 _ _ = ok ?flushed,
      hs : ops.op3 proof = ok (.Ok ?parsed),
      hk : ops.op16 = ok ?splitValue =>
        refine ⟨zero,prepared.2,prepared.1,initial,root,geometry,pending,returned,flushed,parsed,splitValue,?_⟩
        repeat' apply And.intro
        all_goals first | assumption | rfl | (aesop (add simp [bne_iff_ne]))

#print axioms writer_prefix
end AspisR1.VTop_Provenance
end
