import SdkC_Oracle
import Op5T_SelectedPaths
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_GlobalRecovery
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortAllSelectedRecoveryC6

/-- Exact indexed path to GLOBAL first-commitment recovery. Source read
containment and prepared/frame provenance remain explicit, not bundled away.
The exceptional collision event is a conclusion, not an omitted assumption. -/
theorem indexed_recovery_or_collision (H : Bytes → State) (stored : Bytes) (parsed : Parsed)
    (parser : parse stored = some parsed) (q : Fin 22 → Fin 262144)
    (kind pos : Nat) (hk : kind < 3) (hp : pos < 22)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (index q kind pos)))
    (root : BinMerkle32Path.foldPath H path (H (leaf parsed kind pos)) = committedRoot parsed kind)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (reads : ∀ a ∈ BinMerkle32Leaf.fullTrace H path (leaf parsed kind pos), Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (frame : Bytes) (j : Fin 5) (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot parsed kind)) :
    hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log ∨
      recovered log frame parsed kind (index q kind pos) =
        some (OraclePortPackedChoiceC4.payload parsed kind pos) := by
  classical
  by_cases collision : hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log
  · exact Or.inl collision
  right
  obtain ⟨leafBytes,packedWidth,saltWidth⟩ := leaf_fields stored parsed parser kind pos hk hp
  have result := BinRawByteCutRecovery.recover_at_first_commitment SelectedTranscriptParams.params.iv
    H log Q consistent bound collision (tag kind) (width kind)
    (OraclePortPackedChoiceC4.payload parsed kind pos) (salt parsed kind pos) packedWidth saltWidth
    path (committedRoot parsed kind) frame j frameRead rootRead
  have auth : (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput (tag kind) (OraclePortPackedChoiceC4.payload parsed kind pos)
        (salt parsed kind pos)))).2 = committedRoot parsed kind := by
    rw [BinMerkleProgram.eval_leafProgram,← leafBytes]
    exact root
  have contains : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput (tag kind) (OraclePortPackedChoiceC4.payload parsed kind pos)
        (salt parsed kind pos)))).1 a → Read log a := by
    intro a member
    rw [BinMerkleProgram.eval_leafProgram,← leafBytes] at member
    change a ∈ ((BinMerkle32Leaf.fullTrace H path (leaf parsed kind pos)).map
      (fun b => (b,H b))).map Prod.fst at member
    simp only [List.map_map,Function.comp_def,List.map_id] at member
    exact reads a member
  unfold recovered
  rw [result auth contains]
  rfl

/-- This is the single collision loss used above. Q counts ALL distinct
reads in the containing adaptive program, including verifier interactions.
No per-coordinate collision union or hidden clean-event assumption. -/
theorem collision_bound {A : Type} (code : SdkC_Source.Code A) (Q : Nat)
    (budget : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (SdkC_Oracle.program code)).1 ≤ Q) :
    lazyMean (SdkC_Oracle.program code) emptyTable
      (fun view => indicator
        (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv Q view)) ≤
      6 * (Q : ℚ)^2 / (256^32 : ℚ) :=
  BinRawByteCollisionTargets.mass SelectedTranscriptParams.params.iv Q _ budget

#print axioms indexed_recovery_or_collision
#print axioms collision_bound
end AspisR1.SdkC_GlobalRecovery
end
