import Port11PROV_BatchOne

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_FirstOne
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

/-- Full first source record contains the actual driver log after the actual
prover prefix; it is not the later annotation pass. -/
theorem first_logs (rust : OraclePortRuntimeBindingC7.Verifier) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State) :
    ∃ before, (Port6AUTH_SourceCut.first rust P H).1=
      before ++ (eval H (rust (Port6AUTH_SourceCut.first rust P H).2.1)).1 := by
  simp only [Port6AUTH_SourceCut.first,OraclePortFrozen2Join.originalWith_eval]
  exact ⟨_,rfl⟩

/-- Actual first accepted source record, TX1's saved checkpoint, restored
current18 pair and p.gamma powers return. Exact local parser/Prepared/root
provenance supplies canonical batch1 containment in that SAME first log. -/
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
    ∃ pub proof semantic saved p a g folded slice conversion,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧ Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded ∧
      ∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p.queries=q →
        Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q (Port11PROV_Views.nodes proof) 1
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,slice,conversion,earlier,later,hpub,hproof,decoded,tx1,resumed,next,powered,batchRun,range,copy,unwrapped,logs⟩ :=
    Port11PROV_BatchOne.reached decoder adapter ops reserved unwrap rest D hash P H sourceAccepted
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,slice,conversion,hpub,hproof,decoded,tx1,resumed,next,powered,batchRun,range,copy,unwrapped,?_⟩
  intro parsed q len wire binding r0 r1 x read
  have views := Port11PROV_Views.node_bytes proof len parsed wire
  have r2 := Port11PROV_Views.folded ops std proof slice len parsed wire conversion folded range copy unwrapped
  have transported := Port10AUTH_Installed.accepted D hash H occupied sibling leaf occupiedGate siblingGate leafGate
    proof len parsed wire p folded q binding 1#usize (by decide) (Port11PROV_Views.nodes proof) views r0 r1 r2 batchRun
  change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q (Port11PROV_Views.nodes proof) (1#usize).val
    Port4B_BatchJoin.initial)).1 x at read
  rw [transported] at read
  obtain ⟨before,firstLog⟩ := first_logs rust P H
  rw [firstLog,logs]
  simp only [Read,List.map_append,List.mem_append] at read ⊢
  exact Or.inr (Or.inl (Or.inr read))

#print axioms first_logs
#print axioms accepted
end AspisR1.Port11PROV_FirstOne
end
