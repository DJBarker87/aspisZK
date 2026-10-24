import Port6AUTH_SourceCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Compiler
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open Port6AUTH_SourceCut Port6AUTH_Frames
attribute [local irreducible] originalWith OraclePortStoredAdmissionC4.canon lift

theorem maps_eq_builder (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (H : Bytes → State) (p : Parsed)
    (contains : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false)
      (first rust P H).2.1.statement (first rust P H).2.1.proof)).1 a → Read (first rust P H).1 a)
    (targets : ∀ k : Fin 3, BinRawByteCollisionTargets.pred (selectors k)
      (frames D H (first rust P H).2.1.statement (first rust P H).2.1.proof k)=some (committedRoot p k.val)) :
    OraclePortFrozenOrderChecks.maps (first rust P H).1
      (frames D H (first rust P H).2.1.statement (first rust P H).2.1.proof) p=
        build D (view (first rust P H)) := by
  have h0 := targets 0
  have h1 := targets 1
  have h2 := targets 2
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frame D H (first rust P H).2.1.statement (first rust P H).2.1.proof 0)=some (committedRoot p 0) at h0
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frame D H (first rust P H).2.1.statement (first rust P H).2.1.proof 2)=some (committedRoot p 1) at h1
  change BinRawByteCollisionTargets.pred 3
    (RawCutWordsFromView.frame D H (first rust P H).2.1.statement (first rust P H).2.1.proof 30)=some (committedRoot p 2) at h2
  have r0 := OraclePortFrozen2ActualChecks.tail_root _ _ h0
  have r1 := OraclePortFrozen2ActualChecks.tail_root _ _ h1
  have r2 := OraclePortFrozen2ActualChecks.middle_root _ _ h2
  unfold build BinCompiledRunWordStability.wordsFromRun BinCanonicalCutWords.wordsFromRawCuts
  dsimp only
  rw [frame_eq D rust P H contains 0 (by decide),frame_eq D rust P H contains 2 (by decide),
    frame_eq D rust P H contains 30 (by decide),r0,r1,r2]
  rfl

#print axioms maps_eq_builder
end AspisR1.Port6AUTH_Compiler
end
