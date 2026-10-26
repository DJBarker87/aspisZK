import ARQ_FrameReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_PrefixRecovery
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem agreement (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (left right : RawCutProverCompiler.RunView)
    (prior suffixL suffixR : List (Bytes × State))
    (leftLog : left.1 = prior ++ suffixL) (rightLog : right.1 = prior ++ suffixR)
    (pub : left.2.1.1 = right.2.1.1) (proof : left.2.1.2 = right.2.1.2)
    (consistentL : ∀ q ∈ left.1, q.2 = H q.1)
    (consistentR : ∀ q ∈ right.1, q.2 = H q.1)
    (reads : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 a →
      FS2.Duplex.Read prior a)
    (valid : ∀ j, j ≤ 30 → LiteralTranscript.valid j (right.2.1.2 j)) :
    OraclePortRefineJoin.RecoveredInputAgreement left right := by
  have readsL : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 a →
      FS2.Duplex.Read left.1 a := by
    intro addr read
    rw [leftLog]
    change addr ∈ (prior ++ suffixL).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_left _ (reads addr read)
  have readsR : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 a →
      FS2.Duplex.Read right.1 a := by
    intro addr read
    rw [rightLog]
    change addr ∈ (prior ++ suffixR).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_left _ (reads addr read)
  have frames := ARQ_FrameAgreement.frames D H left right pub proof consistentL consistentR
    readsL readsR (fun j below => valid j (by omega))
  apply ARQ_CommonCuts.agreement left right prior suffixL suffixR leftLog rightLog pub frames
  intro row selected
  have small : row ≤ 30 := by rcases selected with rfl | rfl | rfl <;> omega
  unfold RawCommitmentFrameReplay.frameFromView
  rw [SCF_FrameReplay.recorded D H right.1 right.2.1.1 right.2.1.2 consistentR readsR row
    (by omega) (fun j h => valid j (by omega))]
  exact reads _ (ARQ_FrameReads.in_sampler D H _ _ valid row selected)

#print axioms agreement
end AspisR1.ARQ_PrefixRecovery
end
