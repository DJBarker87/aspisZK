import Port6AUTH_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Native
open FS FS2 FS2.Duplex
open MultiproofConeCanonical
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortAllSelectedRecoveryC6

/-- Both native op13 returns belong to the same caller, wire and model Prepared.
BodyMatches for each physical Prepared is the local S1/CK boundary; it contains
no batch acceptance or indexed authentication. Containment refers to these SAME
source calls and remains a named oracle-trace producer obligation. -/
theorem authenticated {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2LeadInterface.S2CallerFacts c (VTop_Checkpoint.digest D) hash H stored pub saved parsed)
    (wireStored : parsed.wire=stored) (parseOK : parse stored=some parsed)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary
      (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H binary occupied sibling leaf)
    (p : Fin 2 → VTop_Stages.verifier.Prepared)
    (a : Fin 2 → AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : Fin 2 → QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : ∀ b, CheckpointBytes4SavedFields.BodyMatches (p b) (a b) pm (am b))
    (modelRoots : ∀ k : Fin 2, pm.roots k=committedRoot parsed k.val)
    (folded : Fin 2 → Array U8 32#usize)
    (foldedInput : ∀ b, bytesOf (folded b).val=bytes (committedRoot parsed 2))
    (reached : ∀ b : Fin 2, c.reached (Port4B_CallerJoin.site (Usize.ofNat b.val (by scalar_tac))))
    (native : ∀ b : Fin 2, Port4B_Install.batch D
      (c.proof (Port4B_CallerJoin.site (Usize.ofNat b.val (by scalar_tac))))
      (p b) (folded b) (Usize.ofNat b.val (by scalar_tac)) hash=ok (.Ok ()))
    (log : List (Bytes × State)) (Q : Nat)
    (contains : ∀ b : Fin 2, ∀ x,
      Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries
        c.nodes b.val Port4B_BatchJoin.initial)).1 x → Read log x)
    (consistent : ∀ x ∈ log, x.2=H x.1)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frames : Fin 3 → Bytes) (selectors : Fin 3 → Fin 5)
    (frameRead : ∀ k, Read log (frames k))
    (rootRead : ∀ k, BinRawByteCollisionTargets.pred (selectors k) (frames k)=some (committedRoot parsed k.val)) :
    ∀ k : Fin 3, ∀ pos, pos<22 →
      recovered log (frames k) parsed k.val (index pm.queries k.val pos)=
        some (OraclePortPackedChoiceC4.payload parsed k.val pos) := by
  have calls (b : Fin 2) := Port4B_CallerJoin.accepted c D hash H stored pub saved parsed facts wireStored
    binary occupied sibling leaf p6 (p b) (a b) pm (am b) (fields b) modelRoots
    (folded b) (foldedInput b) (Usize.ofNat b.val (by scalar_tac)) b.isLt (reached b) (native b)
  obtain ⟨log0,source0,frozen0⟩ := calls 0
  obtain ⟨log1,source1,frozen1⟩ := calls 1
  have uv (b : Fin 2) : (Usize.ofNat b.val (by scalar_tac)).val=b.val := by scalar_tac
  simp only [uv,show (0 : Fin 2).val=0 by decide,show (1 : Fin 2).val=1 by decide] at source0 source1
  have zero : eval H (OraclePortFrozen2.batch parsed pm.queries OraclePortFrozen2.batch0)=(log0,true) :=
    frozen0.symm.trans source0
  have one : eval H (OraclePortFrozen2.batch parsed pm.queries OraclePortFrozen2.batch1)=(log1,true) :=
    frozen1.symm.trans source1
  intro k
  apply Port6AUTH_Recovery.batches H stored parsed parseOK pm.queries log0 log1 log Q zero one
  · intro x hx
    apply contains 0 x
    change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 0 Port4B_BatchJoin.initial)).1 x
    rw [source0]
    exact hx
  · intro x hx
    apply contains 1 x
    change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries c.nodes 1 Port4B_BatchJoin.initial)).1 x
    rw [source1]
    exact hx
  · exact consistent
  · exact bound
  · exact clean
  · exact k.isLt
  · exact frameRead k
  · exact rootRead k

#print axioms authenticated
end AspisR1.Port6AUTH_Native
end
