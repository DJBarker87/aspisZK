import Frozen2StartChargePrefix

/-! Checkpoint addresses are arbitrary bytes and need not be disjoint from
the decoder's start language. The required statement is first-read causality:
if a digest address is a submitted transcript start, it was already read in
the charged prover/sampler prefix. It receives no additional start charge. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Frozen2StartChargeCheckpoint
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortFrozen2Consumer Frozen2StartChargePrefix

/-- Applies to each of the six digest addresses, including proof/public
bytes that an adversary could deliberately format like sampler addresses. -/
theorem no_new_start (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) (a : Bytes)
    (start : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (projected D P)).2.1.1 (eval H (projected D P)).2.1.2 n) = some a) :
    Read (eval H (charged D P)).1 a ∧
      firstIdx a (eval H (projected D P)).1 = firstIdx a (eval H (charged D P)).1 := by
  have read := transcript_start_read D P H n hn a start
  exact ⟨read,first_start_before_terminal D P H a read⟩

#print axioms no_new_start
end AspisR1.Frozen2StartChargeCheckpoint
end
