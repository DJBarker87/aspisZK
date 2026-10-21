import OraclePortBatchDraft

/-! Audit of the inherited whole-proof terminal carrier. A bounded sampler
message cannot hold the compact stored proof. Do not cite all-rejecting
acceptance as a completed verifier or as a premise removal. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortTerminalCarrierAuditC3
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem terminal_length (m : RawCutTranscriptRun.ErasedMessage) :
    (terminalBytes m).length ≤ 3717 := by
  cases m with
  | initial root => exact Nat.zero_le _
  | payload b => exact b.property

theorem parse_impossible (m : RawCutTranscriptRun.ErasedMessage) :
    parse (terminalBytes m) = none := by
  cases hp : parse (terminalBytes m) with
  | none => rfl
  | some p =>
    have hn := ((OraclePortHeader.accepts_iff _).mp (parse_header _ _ hp).1).1
    have bound := terminal_length m
    omega

theorem parseTerminal_impossible (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) : parseTerminal tr m = none := by
  unfold parseTerminal
  rw [parse_impossible]
  rfl

theorem batch_always_rejects (H : Bytes → State)
    (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage) :
    eval H (OraclePortBatchDraft.decision tr m) = ([],false) := by
  simp only [OraclePortBatchDraft.decision,parseTerminal_impossible]
  rfl

#print axioms terminal_length
#print axioms parse_impossible
#print axioms parseTerminal_impossible
#print axioms batch_always_rejects
end AspisR1.OraclePortTerminalCarrierAuditC3
end
