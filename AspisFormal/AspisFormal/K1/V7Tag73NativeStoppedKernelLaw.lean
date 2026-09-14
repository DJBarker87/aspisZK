import AspisFormal.K1.V7Tag73NativeMarkedLaw
import AspisFormal.K1.V7Tag73ForkPairCheckpoint

/-!
# Stopping at a multi-coordinate sampler boundary, on the same compiler law

Unlike a single-digest target, a local event here can read a bounded-retry
sampler's ENTIRE remaining raw tape. The pre-answer selector has no access to
that tape. This supports the actual paired/variable-retry decoder without
pretending one field challenge equals one Digest256 coordinate.

The local kernel bound must be proved for the literal sampler and remaining
resource budget. The theorem does not assume away rejected restorations.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73NativeStoppedKernelLaw
open MeasureTheory
open scoped BigOperators
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73FiniteTapeLaw
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73NativeExposureStep
open AspisK1.V7Tag73ForkPairCheckpoint
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
noncomputable section
variable {A : Type} [Fintype A] [Nonempty A] {State : Type*}

/-- Select before reading; once selected, delegate to the complete local
sampler event. Known remaining budget is allowed in the selection rule. -/
def stoppedKernelHit (next : State → A → State)
    (select : Nat → State → Bool)
    (kernelEvent : (n : Nat) → State → FreshAnswerTape A n → Prop) :
    (n : Nat) → State → FreshAnswerTape A n → Prop
  | 0, s, t => select 0 s = true ∧ kernelEvent 0 s t
  | n + 1, s, t => if select (n+1) s then kernelEvent (n+1) s t
    else stoppedKernelHit next select kernelEvent n (next s t.1) t.2

/-- A first selected local kernel costs its local bound ONCE, even when the
boundary is reached after an adaptive number of ordinary/cache/fork steps. -/
theorem stopped_kernel_probability_le (law : PMF A)
    (next : State → A → State) (select : Nat → State → Bool)
    (kernelEvent : (n : Nat) → State → FreshAnswerTape A n → Prop)
    (epsilon : ENNReal)
    (localBound : ∀ n s, select n s = true →
      (iidTape law n).toOuterMeasure {t | kernelEvent n s t} ≤ epsilon)
    (n : Nat) (s : State) :
    (iidTape law n).toOuterMeasure
      {t | stoppedKernelHit next select kernelEvent n s t} ≤ epsilon := by
  classical
  induction n generalizing s with
  | zero =>
      by_cases selected : select 0 s = true
      · simpa [stoppedKernelHit, selected] using localBound 0 s selected
      · simp [stoppedKernelHit, selected]
  | succ n ih =>
      by_cases selected : select (n+1) s = true
      · simpa [stoppedKernelHit, selected] using
          localBound (n+1) s selected
      · rw [iidTape_event_succ]
        calc
          (∑ a, law a * (iidTape law n).toOuterMeasure
              {tail | stoppedKernelHit next select kernelEvent (n+1) s (a,tail)}) ≤
              ∑ a, law a * epsilon := by
            apply Finset.sum_le_sum
            intro a _
            apply mul_le_mul_left'
            simpa [stoppedKernelHit, selected] using ih (next s a)
          _ = epsilon := by
            rw [← Finset.sum_mul]
            have total : (∑ a, law a) = 1 := by
              simpa only [tsum_fintype] using law.tsum_coe
            rw [total, one_mul]

variable {G : Nat} {R HiddenTape : Type}

/-- Direct two-coordinate law of the ACTUAL native fork and its whole
continuation. Failed/returned terminals remain in the event's sample space. -/
theorem native_fork_terminal_event_disintegrates
    (fuel n : Nat) (history : List QueryRecord)
    (room : history.length + 2 ≤ G) (out adv : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration → SchedulerNativeCursor G R)
    (event : SchedulerNativeTerminal R → Prop) :
    (iidTape (PMF.uniformOfFintype Digest256) (n+2)).toOuterMeasure
      {t | event (runSchedulerNative (fuel+1) (n+2)
        (.forkPair history room out adv template next) t).terminal} =
    ∑ a : Digest256, (PMF.uniformOfFintype Digest256) a *
      ∑ b : Digest256, (PMF.uniformOfFintype Digest256) b *
        (iidTape (PMF.uniformOfFintype Digest256) n).toOuterMeasure
          {tail | event (runSchedulerNative (fuel+1) n
            (next (scheduledForkConfiguration template a b)) tail).terminal} := by
  rw [iidTape_event_succ]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [iidTape_event_succ]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply congrArg ((iidTape (PMF.uniformOfFintype Digest256) n).toOuterMeasure)
  ext tail
  rfl

/-- Exact compiler-law form for an arbitrary pre-answer native boundary. -/
theorem exact_compiler_stopped_kernel_probability_le
    [Fintype HiddenTape] (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters) (fuel : Nat)
    (cursor : HiddenTape → SchedulerNativeCursor G R)
    (select : HiddenTape → Nat → SchedulerNativeCursor G R → Bool)
    (kernelEvent : HiddenTape → (n : Nat) → SchedulerNativeCursor G R →
      FreshAnswerTape Digest256 n → Prop)
    (epsilon : ENNReal)
    (localBound : ∀ hidden n state, select hidden n state = true →
      (iidTape (PMF.uniformOfFintype Digest256) n).toOuterMeasure
        {t | kernelEvent hidden n state t} ≤ epsilon) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      {s | stoppedKernelHit (nativeNext fuel) (select s.1) (kernelEvent s.1)
        (exactCompilerTargetCaps parameters).length (cursor s.1) s.2} ≤ epsilon := by
  change (hiddenTapeUniformFreshJointLaw hiddenLaw
    (exactCompilerTargetCaps parameters).length).toOuterMeasure _ ≤ _
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [← digest_iid_eq_repository]
  exact stopped_kernel_probability_le (PMF.uniformOfFintype Digest256)
    (nativeNext fuel) (select hidden) (kernelEvent hidden) epsilon
    (localBound hidden) (exactCompilerTargetCaps parameters).length (cursor hidden)

#print axioms stopped_kernel_probability_le
#print axioms native_fork_terminal_event_disintegrates
#print axioms exact_compiler_stopped_kernel_probability_le
end
end AspisK1.V7Tag73NativeStoppedKernelLaw
