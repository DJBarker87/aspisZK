import Port10AUTH_Installed
import Port9OR_FirstBatch

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_FirstOne
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

/-- Full first source record contains the actual driver log after the actual
prover prefix; it is not the later annotation pass. -/
theorem first_logs (rust : Port1_StoredCarrier.Verifier) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State) :
    ∃ prefix, (Port6AUTH_SourceCut.first rust P H).1=
      prefix ++ (eval H (rust (Port6AUTH_SourceCut.first rust P H).2.1)).1 := by
  simp only [Port6AUTH_SourceCut.first,OraclePortFrozen2Join.originalWith_eval]
  exact ⟨_,rfl⟩

/-- Actual first accepted source record, TX1's saved checkpoint, restored
current18 pair and p.gamma powers return. Exact local parser/Prepared/root
provenance supplies canonical batch1 containment in that SAME first log. -/
theorem accepted (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
    (sourceAccepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).2.2=true) :
    let impl := Port9OR_Installed.implementation ops reserved unwrap rest
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a g folded,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧ Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      ∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8),
        proof.val.length=57607 → parsed.wire=bytesOf proof.val → Port4B_KeyInstall.queries p.queries=q →
        (∀ b k, b<2 → k<3 → bytesOf (nodes b k).val=OraclePortCompactDraft.slice parsed.wire
          (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k))) →
        Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        folded=encodeState (OraclePortBatchDraft.committedRoot parsed 2) →
        ∀ x, Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 1
          Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust P H).1 x := by
  let impl := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,earlier,later,hpub,hproof,decoded,tx1,resumed,next,powered,batchRun,logs⟩ :=
    Port9OR_FirstBatch.first_batch decoder adapter ops reserved unwrap rest D hash P H sourceAccepted
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,hpub,hproof,decoded,tx1,resumed,next,powered,batchRun,?_⟩
  intro parsed q nodes len wire binding views r0 r1 r2 x read
  have transported := Port10AUTH_Installed.accepted D hash H occupied sibling leaf occupiedGate siblingGate leafGate
    proof len parsed wire p folded q binding 1#usize (by decide) nodes views r0 r1 r2 batchRun
  change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes (1#usize).val
    Port4B_BatchJoin.initial)).1 x at read
  rw [transported] at read
  obtain ⟨prefix,firstLog⟩ := first_logs rust P H
  rw [firstLog,logs]
  simp only [Read,List.map_append,List.mem_append] at read ⊢
  exact Or.inr (Or.inl (Or.inr read))

#print axioms first_logs
#print axioms accepted
end AspisR1.Port10AUTH_FirstOne
end
