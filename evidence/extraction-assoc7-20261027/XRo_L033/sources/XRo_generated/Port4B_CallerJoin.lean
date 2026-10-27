import Port4B_Install

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_CallerJoin
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

def site (batch : Usize) : S2LeadInterface.Site := if batch=0#usize then .batch0 else .batch1

/-- Scoped accepted-only row at the explicit P6 local lowering boundary.
All native children are installed, canonical key binding comes from the SAME
Prepared body provenance, and node views/length/oracle come from Required14.
Parser/model roots, folded input and existence of SAME-cut BodyMatches remain
VISIBLE upstream provenance obligations, not hidden successful-run equalities. -/
theorem accepted {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (facts : S2LeadInterface.S2CallerFacts c (VTop_Checkpoint.digest D) hash H stored pub saved parsed)
    (wireStored : parsed.wire=stored)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H
      binary occupied sibling leaf)
    (p : VTop_Stages.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am)
    (modelRoots : ∀ j : Fin 2, pm.roots j=OraclePortBatchDraft.committedRoot parsed j.val)
    (folded : Array U8 32#usize)
    (foldedInput : bytesOf folded.val=bytes (OraclePortBatchDraft.committedRoot parsed 2))
    (batch : Usize) (hb : batch.val<2) (reached : c.reached (site batch))
    (native : Port4B_Install.batch D (c.proof (site batch)) p folded batch hash=ok (.Ok ())) :
    ∃ log,
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes batch.val
        Port4B_BatchJoin.initial)=(log,true) ∧
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes batch.val
        Port4B_BatchJoin.initial)=
      eval H (OraclePortFrozen2.batch parsed pm.queries
        (if batch.val=0 then OraclePortFrozen2.batch0 else OraclePortFrozen2.batch1)) := by
  have original := facts.proofBytes (site batch) reached
  have size := congrArg List.length original
  simp only [bytesOf,List.length_map] at size
  have length : (c.proof (site batch)).val.length=57607 := size.trans facts.proofLength
  have wire : parsed.wire=bytesOf (c.proof (site batch)).val := wireStored.trans original.symm
  let localP6 : MultiproofConeP6Frozen2Stage.P6Boundary
      (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H binary occupied sibling leaf :=
    {p6 with oracle:=facts.oracle}
  have queryBinding := Port4B_KeyInstall.queries_bound p a pm am fields
  have roots := Port4B_Prepared.roots p a pm am fields
  have installed : Port3_BatchStage.batch (Port4B_VerifyInstall.install (Port4B_KeyInstall.install Port4B_Install.leaves))
      D (c.proof (site batch)) p folded batch hash=ok (.Ok ()) :=
    (Port4B_Install.parent Port4B_Install.leaves D (c.proof (site batch)) p folded batch hash).trans native
  have keys (k : Fin 3) : Port4B_TreeJoin.PackedKeys (Port4B_KeyInstall.install Port4B_Install.leaves)
      p.queries pm.queries batch (Usize.ofNat k.val (by scalar_tac)) :=
    Port4B_KeyInstall.packed Port4B_Install.leaves p.queries pm.queries queryBinding batch _ hb (by have:=k.isLt;scalar_tac)
  obtain ⟨log,source⟩ := Port4B_BatchJoin.accepted (Port4B_KeyInstall.install Port4B_Install.leaves)
    D hash H binary occupied sibling leaf localP6 (c.proof (site batch)) length parsed wire p folded pm.queries batch hb
    c.nodes facts.nodeViews keys (roots.1.trans (congrArg encodeState (modelRoots 0)))
    (roots.2.trans (congrArg encodeState (modelRoots 1)))
    (Port4B_Prepared.digest_of_bytes folded _ foldedInput) installed
  have complete := MultiproofConeP6Frozen2Stage.both_batches (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D))
    hash H binary occupied sibling leaf localP6 parsed pm.queries c.nodes facts.nodeViews
  have success : (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes
      batch.val Port4B_BatchJoin.initial)).2=true := by rw [source]
  refine ⟨log,source,?_⟩
  by_cases zero : batch.val=0
  · simpa only [zero,ite_true] using complete.1 Port4B_BatchJoin.initial (by simpa only [zero] using success)
  · have one : batch.val=1 := by omega
    simpa only [one,show ¬(1:Nat)=0 by decide,if_false] using
      complete.2 Port4B_BatchJoin.initial (by simpa only [one] using success)

#print axioms accepted
end AspisR1.Port4B_CallerJoin
end
