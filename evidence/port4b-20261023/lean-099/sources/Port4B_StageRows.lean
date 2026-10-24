import Port4B_PrepareCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_StageRows
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Explicit remaining S1 Prepared/model provenance, containing no batch
acceptance, oracle history or source/output equality. This is NOT discharged
by the batch row and is NOT a new cryptographic assumption. -/
def PreparedBinding (p : verifier.Prepared) (parsed : OraclePortCompactDraft.Parsed) : Prop :=
  ∃ (a : AspisR1Stage2.verifier.Accumulator) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E),
    CheckpointBytes4SavedFields.BodyMatches p a pm am ∧
    ∀ j : Fin 2, pm.roots j=OraclePortBatchDraft.committedRoot parsed j.val

/-- SAME accepted TX1, no extra successful batch/root read. The only source
child contract retained is S1's still-explicit PreparedBinding on that actual
prepare return. Folded root, batch success, views and reads are derived. -/
theorem tx1 {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (base : Ops) (D : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pubInput : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (stored pub ck : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (facts : S2LeadInterface.S2CallerFacts c (VTop_Checkpoint.digest D) hash H stored pub ck parsed)
    (wireStored : parsed.wire=stored) (reached : c.reached .batch0)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H
      binary occupied sibling leaf)
    (prepare : ∀ zero g p, base.op1=ok zero →
      base.op7 D semantic (c.proof .batch0) hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) → PreparedBinding p parsed)
    (accepted : verifier.candidate.tx1 (Port4B_FoldedCut.install base)
      D semantic pubInput (c.proof .batch0) split hash none=ok (.Ok saved)) :
    ∃ pm log,
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 0 Port4B_BatchJoin.initial)=
        (log,true) ∧
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 0 Port4B_BatchJoin.initial)=
        eval H (OraclePortFrozen2.batch parsed pm.queries OraclePortFrozen2.batch0) := by
  obtain ⟨zero,g,p,root,view,hzero,hprepare,range,copy,batch⟩ :=
    Port4B_PrepareCut.tx1 base D hash semantic pubInput (c.proof .batch0) split saved accepted
  obtain ⟨a,pm,am,fields,roots⟩ := prepare zero g p hzero hprepare
  have original := facts.proofBytes .batch0 reached
  have size := congrArg List.length original
  simp only [bytesOf,List.length_map] at size
  have folded := Port4B_FoldedCut.model (c.proof .batch0) view root (size.trans facts.proofLength)
    parsed (wireStored.trans original.symm) range copy
  obtain ⟨log,source,frozen⟩ := Port4B_CallerJoin.accepted c D hash H stored pub ck parsed facts wireStored
    binary occupied sibling leaf p6 p a pm am fields roots root folded 0#usize (by decide) reached batch
  exact ⟨pm,log,source,by simpa using frozen⟩

/-- SAME accepted authenticated TX2: p is its actual resume return and the
folded copy/batch1 are from its continuation, never another successful reader. -/
theorem tx2 {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (base : Ops) (D : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (pubInput checkpoint : Slice U8) (stored pub ck : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (facts : S2LeadInterface.S2CallerFacts c (VTop_Checkpoint.digest D) hash H stored pub ck parsed)
    (wireStored : parsed.wire=stored) (reached : c.reached .batch1)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H
      binary occupied sibling leaf)
    (resume : ∀ p a, base.op18 D checkpoint (c.proof .batch1) pubInput .S2 hash=ok (.Ok (p,a)) → PreparedBinding p parsed)
    (accepted : verifier.candidate.tx2_authenticated (Port4B_FoldedCut.install base)
      D pubInput (c.proof .batch1) checkpoint hash none=ok (.Ok ())) :
    ∃ pm log,
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 1 Port4B_BatchJoin.initial)=
        (log,true) ∧
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 1 Port4B_BatchJoin.initial)=
        eval H (OraclePortFrozen2.batch parsed pm.queries OraclePortFrozen2.batch1) := by
  obtain ⟨p,a,root,view,read,range,copy,batch⟩ :=
    Port4B_FoldedCut.tx2 base D hash pubInput (c.proof .batch1) checkpoint accepted
  obtain ⟨aModel,pm,am,fields,roots⟩ := resume p a read
  have original := facts.proofBytes .batch1 reached
  have size := congrArg List.length original
  simp only [bytesOf,List.length_map] at size
  have folded := Port4B_FoldedCut.model (c.proof .batch1) view root (size.trans facts.proofLength)
    parsed (wireStored.trans original.symm) range copy
  obtain ⟨log,source,frozen⟩ := Port4B_CallerJoin.accepted c D hash H stored pub ck parsed facts wireStored
    binary occupied sibling leaf p6 p aModel pm am fields roots root folded 1#usize (by decide) reached batch
  exact ⟨pm,log,source,by simpa using frozen⟩

#print axioms tx1
#print axioms tx2
end AspisR1.Port4B_StageRows
end
