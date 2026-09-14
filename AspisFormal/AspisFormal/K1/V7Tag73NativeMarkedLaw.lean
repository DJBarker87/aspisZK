import AspisFormal.K1.V7Tag73NativeExposureStep
import AspisFormal.K1.V7Tag73FirstMarkedExposure
import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition

/-!
# First marked native exposure, on exactCompilerJointLaw

The source connection is the literal native step theorem, and the law connection
is the repository's independent hidden-tape/uniform-answer construction.

This proves a REAL same-law bound for the marked scheduler event. It does not
assert that K1.3 failure is contained in that event. That is a separate source
and extraction argument, not another law equality to assume.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73NativeMarkedLaw
open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73NativeExposureStep
open AspisK1.V7Tag73FirstMarkedExposure
open AspisK1.V7Tag73FiniteTapeLaw
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
noncomputable section
variable {G : Nat} {R HiddenTape : Type}

/-- `cursor hidden` and `mark hidden` are fixed before master answers exist. -/
def compilerMarkedEvent (parameters : ExactCompilerResourceParameters)
    (fuel : Nat) (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256)) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {s | firstMarkedHit (nativeNext fuel) (mark s.1)
      (exactCompilerTargetCaps parameters).length (cursor s.1) s.2}

theorem exact_compiler_first_marked_probability_le
    [Fintype HiddenTape] (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters) (fuel : Nat)
    (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256))
    (error : ENNReal)
    (localBound : ∀ hidden state target, mark hidden state = some target →
      (PMF.uniformOfFintype Digest256).toOuterMeasure (target : Set Digest256) ≤ error) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (compilerMarkedEvent parameters fuel cursor mark) ≤ error := by
  change (hiddenTapeUniformFreshJointLaw hiddenLaw
    (exactCompilerTargetCaps parameters).length).toOuterMeasure _ ≤ _
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [← digest_iid_eq_repository]
  exact firstMarked_probability_le (PMF.uniformOfFintype Digest256)
    (nativeNext fuel) (mark hidden) error (localBound hidden)
    (exactCompilerTargetCaps parameters).length (cursor hidden)

/-- Arbitrary clean/accepting filters can only remove mass; no conditional
uniformity after that filter is asserted. -/
theorem exact_compiler_restricted_first_marked_probability_le
    [Fintype HiddenTape] (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters) (fuel : Nat)
    (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256))
    (error : ENNReal)
    (localBound : ∀ hidden state target, mark hidden state = some target →
      (PMF.uniformOfFintype Digest256).toOuterMeasure (target : Set Digest256) ≤ error)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (clean ∩ compilerMarkedEvent parameters fuel cursor mark) ≤ error :=
  ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
    Set.inter_subset_right).trans
      (exact_compiler_first_marked_probability_le hiddenLaw parameters fuel
        cursor mark error localBound)

/-- A deterministic inclusion consumes the proved same-law bound. The
inclusion is intentionally visible and must name a genuine failure event. -/
theorem covered_event_le_first_marked
    [Fintype HiddenTape] (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters) (fuel : Nat)
    (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256))
    (error : ENNReal)
    (localBound : ∀ hidden state target, mark hidden state = some target →
      (PMF.uniformOfFintype Digest256).toOuterMeasure (target : Set Digest256) ≤ error)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : event ⊆ compilerMarkedEvent parameters fuel cursor mark) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤ error :=
  ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono covered).trans
    (exact_compiler_first_marked_probability_le hiddenLaw parameters fuel
      cursor mark error localBound)

#print axioms exact_compiler_first_marked_probability_le
#print axioms exact_compiler_restricted_first_marked_probability_le
#print axioms covered_event_le_first_marked
end
end AspisK1.V7Tag73NativeMarkedLaw
