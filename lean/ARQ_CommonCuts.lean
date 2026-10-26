import SCF_Recovery
set_option autoImplicit false
namespace AspisR1.ARQ_CommonCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Arbitrary DIFFERENT suffixes preserve every cut already reached in the
identical chronological prior. No sublist/event transport is used. -/
theorem cut (prior left right : List (Bytes × State)) (frame : Bytes)
    (read : FS2.Duplex.Read prior frame) :
    BinRawByteCutRecovery.cut (prior ++ left) frame =
      BinRawByteCutRecovery.cut (prior ++ right) frame := by
  rw [SCE_ReplayTable.cut_append prior left frame read,SCE_ReplayTable.cut_append prior right frame read]

/-- Same semantic public and exact replayed frames on a common read prefix
suffice for recovery despite arbitrary extra adversary reads in either suffix. -/
theorem agreement (left right : RawCutProverCompiler.RunView)
    (prior suffixL suffixR : List (Bytes × State))
    (leftLog : left.1 = prior ++ suffixL) (rightLog : right.1 = prior ++ suffixR)
    (pub : left.2.1.1 = right.2.1.1)
    (frames : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      RawCommitmentFrameReplay.frameFromView left row = RawCommitmentFrameReplay.frameFromView right row)
    (reads : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      FS2.Duplex.Read prior (RawCommitmentFrameReplay.frameFromView right row)) :
    OraclePortRefineJoin.RecoveredInputAgreement left right := by
  apply SCF_Recovery.agreement left right pub frames
  intro row selected
  rw [leftLog,rightLog]
  exact cut prior suffixL suffixR _ (reads row selected)

#print axioms cut
#print axioms agreement
end AspisR1.ARQ_CommonCuts
