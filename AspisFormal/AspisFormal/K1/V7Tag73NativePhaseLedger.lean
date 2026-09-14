import AspisFormal.K1.V7Tag73NativeMarkedLaw

/-!
# Finite stage charges on ONE compiler measure

A phase has its own once-only observer. The union bound is over the explicitly
listed phases, not every stored node. Reusing the same phase label twice pays
it twice. Distinct phase labels need not observe independent random variables.

This is the intended arithmetic destination for K1.3 q16/one-fold/batch/alpha,
K1.4 width-29, and K1.5's fixed categories. Their actual source coverage and
resource/rejection terms must still be proved; this file does not create them.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73NativePhaseLedger
open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73NativeMarkedLaw
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
noncomputable section
variable {S Phase : Type*}

def finiteEventUnion (events : Phase → Set S) : List Phase → Set S
  | [] => ∅
  | p :: rest => events p ∪ finiteEventUnion events rest

def finiteCharge (charge : Phase → ENNReal) : List Phase → ENNReal
  | [] => 0
  | p :: rest => charge p + finiteCharge charge rest

theorem finiteEventUnion_mem (events : Phase → Set S) (phases : List Phase) (s : S) :
    s ∈ finiteEventUnion events phases ↔ ∃ p ∈ phases, s ∈ events p := by
  induction phases with
  | nil => simp [finiteEventUnion]
  | cons p rest ih => simp [finiteEventUnion, ih, or_and_right, exists_or]

theorem finiteEventUnion_measure_le (mu : OuterMeasure S)
    (events : Phase → Set S) (charge : Phase → ENNReal)
    (phases : List Phase) (bound : ∀ p ∈ phases, mu (events p) ≤ charge p) :
    mu (finiteEventUnion events phases) ≤ finiteCharge charge phases := by
  induction phases with
  | nil => simp [finiteEventUnion, finiteCharge]
  | cons p rest ih =>
      exact (measure_union_le _ _).trans
        (add_le_add (bound p (by simp)) (ih (fun q hq => bound q (by simp [hq]))))

variable {HiddenTape R : Type} [Fintype HiddenTape] {G : Nat}

/-- Every term is evaluated under exactly exactCompilerJointLaw. -/
theorem native_phase_union_probability_le
    (hiddenLaw : PMF HiddenTape) (parameters : ExactCompilerResourceParameters)
    (fuel : Nat) (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : Phase → HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256))
    (charge : Phase → ENNReal) (phases : List Phase)
    (localBound : ∀ phase ∈ phases, ∀ hidden state target,
      mark phase hidden state = some target →
      (PMF.uniformOfFintype Digest256).toOuterMeasure (target : Set Digest256) ≤ charge phase) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (finiteEventUnion (fun phase => compilerMarkedEvent parameters fuel cursor (mark phase)) phases) ≤
      finiteCharge charge phases := by
  apply finiteEventUnion_measure_le
  intro phase present
  exact exact_compiler_first_marked_probability_le hiddenLaw parameters fuel
    cursor (mark phase) (charge phase) (localBound phase present)

/-- Honest stage bound: resource/rejection/selection failures are a named
actual event, not silently assigned a field-root cardinality. -/
theorem source_stage_probability_le_with_residual
    (hiddenLaw : PMF HiddenTape) (parameters : ExactCompilerResourceParameters)
    (fuel : Nat) (cursor : HiddenTape → SchedulerNativeCursor G R)
    (mark : Phase → HiddenTape → SchedulerNativeCursor G R → Option (Finset Digest256))
    (charge : Phase → ENNReal) (phases : List Phase)
    (localBound : ∀ phase ∈ phases, ∀ hidden state target,
      mark phase hidden state = some target →
      (PMF.uniformOfFintype Digest256).toOuterMeasure (target : Set Digest256) ≤ charge phase)
    (sourceFailure residual : Set (ExactCompilerSample HiddenTape parameters))
    (covered : sourceFailure ⊆ residual ∪
      finiteEventUnion (fun phase => compilerMarkedEvent parameters fuel cursor (mark phase)) phases) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure sourceFailure ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure residual + finiteCharge charge phases := by
  let mu := (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  exact (mu.mono covered).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (native_phase_union_probability_le hiddenLaw parameters
      fuel cursor mark charge phases localBound)))

#print axioms finiteEventUnion_mem
#print axioms finiteEventUnion_measure_le
#print axioms native_phase_union_probability_le
#print axioms source_stage_probability_le_with_residual
end
end AspisK1.V7Tag73NativePhaseLedger
