import Port4B_VerifyInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_VerifyRun
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConePhysicalTransport MultiproofConePhysicalViews

/-- The installed P6 owned verifier success determines the SAME physical
source return and scratch. P6Boundary stays named; no successful level, root
or output/log agreement hypothesis is introduced. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest D) hash H
      binary occupied sibling leaf)
    (root : Array U8 32#usize) (s : reference.Scratch) (nodes : Slice U8)
    (well : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst))
    (words : nodes.val.length%32=0) (size : nodes.val.length≤5504)
    (outIdx : Indices) (outVal : Values)
    (returned : (Port4B_VerifyInstall.install base).op10 D hash
      Port3_NativeBatchBody.multiproof.Arity.Two root s.idx s.val s.n nodes=ok (true,outIdx,outVal)) :
    ∃ final,
      (eval H (MultiproofConeP6Verify.verifyState
        (MultiproofConeP6Callbacks.nodeWith occupied sibling) root nodes {s with «at»:=0#usize})).2=(true,final) ∧
      final.idx=outIdx ∧ final.val=outVal := by
  change (do let (accepted,out) ← reference.verify_owned (Port4B_VerifyInstall.digest D) hash root {s with «at»:=0#usize} nodes; ok (accepted,out.idx,out.val))=ok (true,outIdx,outVal) at returned
  obtain ⟨⟨accepted,out⟩,verify,returned⟩ := Port3_PushFrame.bind_success _ _ _ returned
  have same := Result.ok.inj returned
  simp only [Prod.mk.injEq] at same
  rcases same with ⟨truth,indices,values⟩
  subst accepted
  rw [←Port4B_VerifyInstall.normalization] at verify
  obtain ⟨height,rootOK⟩ := Port4B_VerifyInstall.wrapper_success _ root {s with «at»:=0#usize} out nodes verify
  have length : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by
    simp only [List.length_map,MultiproofConeRootGuard.live_length]
  have positive : 0<s.n.val := by
    by_contra bad
    have empty : (live s 0 s.n.val).map Prod.fst=[] := List.length_eq_zero_iff.mp (by omega)
    exact well.1 empty
  have domain : MultiproofConeLevelIteration.Domain nodes {s with «at»:=0#usize} :=
    ⟨positive,by have bound:=well.2.1;omega,by simp⟩
  have interpreted :
      (eval H (transport (MultiproofConePhysicalLevels.levels 18 {s with «at»:=0#usize} nodes))).2=
        ok (.Done out) := by
    rw [transport_observation]
    exact (MultiproofConePhysicalLevels.eighteen_result (Port4B_VerifyInstall.digest D) hash
      (rawOracle H) p6.oracle _ nodes domain).trans height
  have guard : OraclePortFrozenOrder.wellFormed
      ((live {s with «at»:=0#usize} 0 s.n.val).map Prod.fst) ∧ nodes.val.length%32=0 := ⟨well,words⟩
  have physical : (eval H (MultiproofConeVerifyState.verifyState root nodes {s with «at»:=0#usize})).2=
      (true,out) := by
    simp only [MultiproofConeVerifyState.verifyState,if_pos guard,eval_bind,eval,interpreted,
      MultiproofConeVerifyState.finishState,rootOK]
  have lower := MultiproofConeP6Verify.verifyState_eq (Port4B_VerifyInstall.digest D) hash H p6.oracle
    (MultiproofConeP6Callbacks.nodeWith occupied sibling)
    (MultiproofConeP6Callbacks.node_gate (rawOracle H) occupied sibling p6.occupied_parent p6.sibling_parent)
    root nodes size {s with «at»:=0#usize} rfl
  exact ⟨out,(congrArg Prod.snd lower).trans physical,indices,values⟩

#print axioms accepted
end AspisR1.Port4B_VerifyRun
end
