import AspisFormal.K1.V7Tag73NativeExposureStep

/-!
# Exact atomic pair and a checkpoint that excludes its new answers

A checkpoint may depend on the old accepted root. It must be fixed before the
NEW fork pair. This is NOT equality of root and restored child challenges.
The checkpoint deliberately excludes template.forkOutput/template.forkAdvance:
those stale fields are overwritten by scheduledForkConfiguration.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73ForkPairCheckpoint
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73NativeExposureStep
noncomputable section
variable {G : Nat} {R : Type}

structure PairCheckpoint where
  frozenHistory : List QueryRecord
  outputInput : ShaInput
  advanceInput : ShaInput

/-- Snapshot only at the pair-output boundary, before the first new answer. -/
def checkpoint? (fuel : Nat) (cursor : SchedulerNativeCursor G R) :
    Option PairCheckpoint :=
  match seekSchedulerNativeExposure fuel cursor with
  | .forkOutput history _room out adv _template _next =>
      some ⟨history, out, adv⟩
  | _ => none

theorem checkpoint_of_pair (fuel : Nat) (history : List QueryRecord)
    (room : history.length + 2 ≤ G) (out adv : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration → SchedulerNativeCursor G R) :
    checkpoint? (fuel + 1) (.forkPair history room out adv template next) =
      some ⟨history, out, adv⟩ := by rfl

/-- BOTH programmed answers, not just the output half, reach the continuation. -/
theorem native_pair_two_steps (fuel : Nat) (history : List QueryRecord)
    (room : history.length + 2 ≤ G) (out adv : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration → SchedulerNativeCursor G R)
    (a b : Digest256) :
    nativeNext (fuel + 1)
      (nativeNext (fuel + 1) (.forkPair history room out adv template next) a) b =
      next (scheduledForkConfiguration template a b) := by rfl

/-- Exact suffix replay after the two atomic coordinates, for arbitrary tail. -/
theorem native_pair_terminal_suffix (fuel n : Nat) (history : List QueryRecord)
    (room : history.length + 2 ≤ G) (out adv : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration → SchedulerNativeCursor G R)
    (a b : Digest256) (tail : FreshAnswerTape Digest256 n) :
    (runSchedulerNative (fuel + 1) (n + 2)
      (.forkPair history room out adv template next) (a, (b, tail))).terminal =
    (runSchedulerNative (fuel + 1) n
      (next (scheduledForkConfiguration template a b)) tail).terminal := by rfl

/-- Prefix-derived checkpoint equality never needs to compare new answers. -/
theorem checkpoint_prefix_congr (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (left right : List Digest256) (same : left = right) :
    checkpoint? fuel (advancePrefix fuel cursor left) =
      checkpoint? fuel (advancePrefix fuel cursor right) := by rw [same]

/-- Reads really taken from this checkpoint are invariant under arbitrary
changes to the unconsumed pair and suffix. Source must provide the read map. -/
theorem checkpoint_read_congr {Data : Type*}
    (read : PairCheckpoint → Data) (left right : PairCheckpoint)
    (same : left = right) : read left = read right := congrArg read same

#print axioms checkpoint_of_pair
#print axioms native_pair_two_steps
#print axioms native_pair_terminal_suffix
#print axioms checkpoint_prefix_congr
end
end AspisK1.V7Tag73ForkPairCheckpoint
