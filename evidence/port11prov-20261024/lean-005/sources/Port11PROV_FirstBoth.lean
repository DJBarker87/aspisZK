import Port10AUTH_TX1Reached
import Port11PROV_FirstOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_FirstBoth
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical
theorem accepted (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (std : Port1_Library.TrustedStd ops)
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
      folded=folded0 ∧
      (∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p0.queries=q →
        Port3_BatchStage.root0 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q (Port11PROV_Views.nodes proof) 0
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x) ∧
      (∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p.queries=q →
        Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q (Port11PROV_Views.nodes proof) 1
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x) := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,slice1,conversion1,hpub,hproof,decoded,tx1,resumed,next,powered,native1,range1,copy1,unwrap1,containsOne⟩ :=
    Port11PROV_FirstOne.accepted decoder adapter ops reserved unwrap rest D hash P H std occupied sibling leaf
      occupiedGate siblingGate leafGate sourceAccepted
  obtain ⟨p0,a0,g0,folded0,slice,conversion,earlier,readRoot,arrayRoot,unwrapRoot,native0,suffix,zeroLogs⟩ :=
    Port10AUTH_TX1Reached.accepted ops reserved unwrap rest D hash semantic pub proof saved H tx1
  have sameSlice : slice1=slice := Result.ok.inj (range1.symm.trans readRoot)
  have sameConversion : conversion1=conversion := Result.ok.inj ((sameSlice ▸ copy1).symm.trans arrayRoot)
  have sameRoot : folded=folded0 := Result.ok.inj ((sameConversion ▸ unwrap1).symm.trans unwrapRoot)
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,p0,a0,g0,folded0,slice,conversion,
    hpub,hproof,decoded,tx1,resumed,next,powered,native1,readRoot,arrayRoot,unwrapRoot,native0,suffix,sameRoot,?_,containsOne⟩
  intro parsed q len wire binding r0 r1 x read
  have views := Port11PROV_Views.node_bytes proof len parsed wire
  have r2 := Port11PROV_Views.folded ops std proof slice len parsed wire conversion folded0 readRoot arrayRoot unwrapRoot
  have transported := Port10AUTH_Installed.accepted D hash H occupied sibling leaf occupiedGate siblingGate leafGate
    proof len parsed wire p0 folded0 q binding 0#usize (by decide) (Port11PROV_Views.nodes proof) views r0 r1 r2 native0
  change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q (Port11PROV_Views.nodes proof) (0#usize).val
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
  obtain ⟨before,firstLog⟩ := Port11PROV_FirstOne.first_logs rust P H
  rw [firstLog,rustLogs,zeroLogs]
  simp only [Read,List.map_append,List.mem_append] at read ⊢
  exact Or.inr (Or.inl (Or.inl (Or.inr read)))

#print axioms accepted
end AspisR1.Port11PROV_FirstBoth
end

