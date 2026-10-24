import Port10AUTH_TX1Reached
import Port10AUTH_FirstOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_FirstBoth
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical
theorem accepted (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
    (sourceAccepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).2.2=true) :
    let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a g folded p0 a0 g0 folded0 slice conversion,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧ Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded0 ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p0 folded0 0#usize hash=ok (.Ok ()) ∧
      (eval H (interpret impl (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p0 a0 g0 (.Ok ())))).2=ok (.Ok saved) ∧
      (∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p0.queries=q →
        (∀ b k, b<2 → k<3 → bytesOf (nodes b k).val=OraclePortCompactDraft.slice parsed.wire
          (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k))) →
        Port3_BatchStage.root0 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        folded0=encodeState (OraclePortBatchDraft.committedRoot parsed 2) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 0
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x) ∧
      (∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p.queries=q →
        (∀ b k, b<2 → k<3 → bytesOf (nodes b k).val=OraclePortCompactDraft.slice parsed.wire
          (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k))) →
        Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        folded=encodeState (OraclePortBatchDraft.committedRoot parsed 2) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 1
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x) := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,hpub,hproof,decoded,tx1,resumed,next,powered,native1,containsOne⟩ :=
    Port10AUTH_FirstOne.accepted decoder adapter ops reserved unwrap rest D hash P H occupied sibling leaf
      occupiedGate siblingGate leafGate sourceAccepted
  obtain ⟨p0,a0,g0,folded0,slice,conversion,earlier,readRoot,arrayRoot,unwrapRoot,native0,suffix,zeroLogs⟩ :=
    Port10AUTH_TX1Reached.accepted ops reserved unwrap rest D hash semantic pub proof saved H tx1
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,p0,a0,g0,folded0,slice,conversion,
    hpub,hproof,decoded,tx1,resumed,next,powered,native1,readRoot,arrayRoot,unwrapRoot,native0,suffix,?_,containsOne⟩
  intro parsed q nodes len wire binding views r0 r1 r2 x read
  have transported := Port10AUTH_Installed.accepted D hash H occupied sibling leaf occupiedGate siblingGate leafGate
    proof len parsed wire p0 folded0 q binding 0#usize (by decide) nodes views r0 r1 r2 native0
  change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes (0#usize).val
    Port4B_BatchJoin.initial)).1 x at read
  rw [transported] at read
  change Port1_Driver.asSlice input.statement.pubBytes=some pub at hpub
  change Port1_Driver.asSlice input.stored=some proof at hproof
  have entry : rust input=Port1_Driver.stages impl D hash semantic pub proof := by
    change Port1_Driver.rust adapter impl D hash input=_
    simp only [Port1_Driver.rust,hpub,hproof,decoded]
  have first := Port7CLEAN_Driver.first_accepted decoder adapter impl D hash P H sourceAccepted
  change (eval H (rust input)).2=true at first
  have stages : (eval H (Port1_Driver.stages impl D hash semantic pub proof)).2=true := by
    rw [entry] at first
    exact first
  obtain ⟨otherSaved,tx1Again,tx2,stageLogs⟩ := Port7CLEAN_Driver.accepted_stages impl D hash semantic pub proof H stages
  have same : otherSaved=saved := core.result.Result.Ok.inj (Result.ok.inj (tx1Again.symm.trans tx1))
  subst otherSaved
  have rustLogs := (congrArg (fun program => (eval H program).1) entry).trans stageLogs
  obtain ⟨before,firstLog⟩ := Port10AUTH_FirstOne.first_logs rust P H
  rw [firstLog,rustLogs,zeroLogs]
  simp only [Read,List.map_append,List.mem_append] at read ⊢
  exact Or.inr (Or.inl (Or.inl (Or.inr read)))

#print axioms accepted
end AspisR1.Port10AUTH_FirstBoth
end

-- Focused final consumer/import audit; not a frozen-manifest replay.
set_option pp.proofs false
#print AspisR1.Port10AUTH_Batch.accepted
#print axioms AspisR1.Port10AUTH_Batch.accepted
#print AspisR1.Port10AUTH_BatchLog.bind_success
#print axioms AspisR1.Port10AUTH_BatchLog.bind_success
#print AspisR1.Port10AUTH_BatchLog.logs
#print axioms AspisR1.Port10AUTH_BatchLog.logs
#print AspisR1.Port10AUTH_Dictionary.loop
#print axioms AspisR1.Port10AUTH_Dictionary.loop
#print AspisR1.Port10AUTH_Dictionary.tree
#print axioms AspisR1.Port10AUTH_Dictionary.tree
#print AspisR1.Port10AUTH_Dictionary.batch
#print axioms AspisR1.Port10AUTH_Dictionary.batch
#print AspisR1.Port10AUTH_FirstBoth.accepted
#print axioms AspisR1.Port10AUTH_FirstBoth.accepted
#print AspisR1.Port10AUTH_FirstOne.first_logs
#print axioms AspisR1.Port10AUTH_FirstOne.first_logs
#print AspisR1.Port10AUTH_FirstOne.accepted
#print axioms AspisR1.Port10AUTH_FirstOne.accepted
#print AspisR1.Port10AUTH_Installed.accepted
#print axioms AspisR1.Port10AUTH_Installed.accepted
#print AspisR1.Port10AUTH_Leaf.lift_bind
#print axioms AspisR1.Port10AUTH_Leaf.lift_bind
#print AspisR1.Port10AUTH_Leaf.pure_trace
#print axioms AspisR1.Port10AUTH_Leaf.pure_trace
#print AspisR1.Port10AUTH_Leaf.active
#print axioms AspisR1.Port10AUTH_Leaf.active
#print AspisR1.Port10AUTH_Leaf.leaf_trace
#print axioms AspisR1.Port10AUTH_Leaf.leaf_trace
#print AspisR1.Port10AUTH_Leaf.accepted_trace
#print axioms AspisR1.Port10AUTH_Leaf.accepted_trace
#print AspisR1.Port10AUTH_Leaves.accepted
#print axioms AspisR1.Port10AUTH_Leaves.accepted
#print AspisR1.Port10AUTH_Levels.rows
#print axioms AspisR1.Port10AUTH_Levels.rows
#print AspisR1.Port10AUTH_Levels.level
#print axioms AspisR1.Port10AUTH_Levels.level
#print AspisR1.Port10AUTH_Levels.levels
#print axioms AspisR1.Port10AUTH_Levels.levels
#print AspisR1.Port10AUTH_Levels.accepted
#print axioms AspisR1.Port10AUTH_Levels.accepted
#print AspisR1.Port10AUTH_LoopTail.accepted
#print axioms AspisR1.Port10AUTH_LoopTail.accepted
#print AspisR1.Port10AUTH_Node.parent
#print axioms AspisR1.Port10AUTH_Node.parent
#print AspisR1.Port10AUTH_Node.node
#print axioms AspisR1.Port10AUTH_Node.node
#print AspisR1.Port10AUTH_Node.accepted
#print axioms AspisR1.Port10AUTH_Node.accepted
#print AspisR1.Port10AUTH_Selected.iteration
#print axioms AspisR1.Port10AUTH_Selected.iteration
#print AspisR1.Port10AUTH_TX1Cut.source
#print axioms AspisR1.Port10AUTH_TX1Cut.source
#print AspisR1.Port10AUTH_TX1Reached.accepted
#print axioms AspisR1.Port10AUTH_TX1Reached.accepted
#print AspisR1.Port10AUTH_Tail.accepted
#print axioms AspisR1.Port10AUTH_Tail.accepted
#print AspisR1.Port10AUTH_TerminalCut.map_log
#print axioms AspisR1.Port10AUTH_TerminalCut.map_log
#print AspisR1.Port10AUTH_TerminalCut.accepted
#print axioms AspisR1.Port10AUTH_TerminalCut.accepted
#print AspisR1.Port10AUTH_Total.replace
#print axioms AspisR1.Port10AUTH_Total.replace
#print AspisR1.Port10AUTH_Total.accepted
#print axioms AspisR1.Port10AUTH_Total.accepted
#print AspisR1.Port10AUTH_Trace.trace_bind
#print axioms AspisR1.Port10AUTH_Trace.trace_bind
#print AspisR1.Port10AUTH_Trace.run_of_trace
#print axioms AspisR1.Port10AUTH_Trace.run_of_trace
#print AspisR1.Port10AUTH_Trace.trace_lift
#print axioms AspisR1.Port10AUTH_Trace.trace_lift
#print AspisR1.Port10AUTH_Tree.accepted
#print axioms AspisR1.Port10AUTH_Tree.accepted
#print AspisR1.Port10AUTH_Verify.accepted
#print axioms AspisR1.Port10AUTH_Verify.accepted
#print AspisR1.Port10AUTH_VerifyCut.after_success
#print axioms AspisR1.Port10AUTH_VerifyCut.after_success
#print AspisR1.Port10AUTH_VerifyCut.accepted
#print axioms AspisR1.Port10AUTH_VerifyCut.accepted
#print AspisR1.Port10AUTH_VerifyProjection.log
#print axioms AspisR1.Port10AUTH_VerifyProjection.log
#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary
#print AspisR1.MultiproofConeP6Callbacks.ParentGate
#print AspisR1.MultiproofConeP6Batch.LeafGate
#print AspisR1.Port4B_TreeJoin.PackedKeys
#print AspisR1.CheckpointBytes4SavedFields.BodyMatches
#print AspisR1.Port10AUTH_Total.dictionary
