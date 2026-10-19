import GSWideExactAgreementInputs
import GSInitialMessageCandidateFilter
import GSFinalMessageCandidateFilter
import GSActualEncoderGRSBridge
import InitialForwardEncoderBaseV9
import RRFinalMessageRecovery
import WideExactGRSInstantiationV5
import AspisFormal.V7ExactOneFoldDomains
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSRuntimeDistanceEncoderBridge

open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV7ExactOneFoldDomains
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.InitialForwardEncoderBaseV9
open AspisWide.GSInitialMessageCandidateFilter
open AspisWide.GSFinalMessageCandidateFilter
open AspisWideTower
open AspisR1.RRFinalMessageRecovery

variable [Field WideExact] [BEq WideExact] [LawfulBEq WideExact]
  [DecidableEq WideExact] [NeZero (2 : WideExact)]
  [Algebra (ZMod P) WideExact] [Fintype WideExact]
  [LawfulBEq (CPolynomial WideExact)]

/-- Literal, executable stereographic evaluation point used by the initial
released encoder. This avoids evaluating the noncomputable GRS conversion
record in runtime code. -/
def initialRuntimePoint (i : Fin 1048576) : WideExact :=
  algebraMap (ZMod P) WideExact
    ((storedInitialCirclePoint20 i).1.2 /
      (1 + X (storedInitialCirclePoint20 i)))

/-- Evaluate the actual computable initial CPolynomial, with the released
512-power column multiplier expressed directly in field operations. -/
def initialRuntimeEncoder (m : InitialMessage WideExact) : InitialWord WideExact :=
  fun i =>
    ((1 + (initialRuntimePoint i) ^ 2) ^ 512)⁻¹ *
      CPolynomial.eval (initialRuntimePoint i) (encodeInitialC m)

/-- Literal, executable final line evaluation with multiplier one. -/
def finalRuntimePoint (i : Fin 262144) : WideExact :=
  algebraMap (ZMod P) WideExact (storedFirstLineX18 i)

def finalRuntimeEncoder (m : FinalMessage WideExact) : FinalWord WideExact :=
  fun i => CPolynomial.eval (finalRuntimePoint i) (encodeFinal m)

theorem initialRuntimePoint_eq_conversion (i : Fin 1048576) :
    initialRuntimePoint i = initialConversion.points i := by
  change algebraMap (ZMod P) WideExact
      ((storedInitialCirclePoint20 i).1.2 /
        (1 + X (storedInitialCirclePoint20 i))) = initialConversion.points i
  rw [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
    AspisWide.GRSConversion.exactCircleGRSPoint_eq_stored]

theorem finalRuntimePoint_eq_conversion (i : Fin 262144) :
    finalRuntimePoint i = finalConversion.points i := by
  rfl

theorem initialRuntimeEncoder_eq_released (m : InitialMessage WideExact) :
    initialRuntimeEncoder m =
      AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) m := by
  funext i
  have hp := initialRuntimePoint_eq_conversion i
  have hm : ((1 + (initialRuntimePoint i) ^ 2) ^ 512)⁻¹ =
      initialConversion.multipliers i := by
    simp [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
      AspisWide.GRSConversion.exactCircleGRSMultiplier, hp]
  have he : CPolynomial.eval (initialRuntimePoint i) (encodeInitialC m) =
      (initialConversion.messagePolynomial m).eval (initialConversion.points i) := by
    rw [CPolynomial.eval_toPoly,
      AspisWide.GSActualEncoderGRSBridge.initial_encode_to_grs_messagePolynomial,
      hp]
  have hc := initialConversion.coordinate_identity m i
  change AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) m i =
      initialConversion.multipliers i *
        (initialConversion.messagePolynomial m).eval
          (initialConversion.points i) at hc
  dsimp [initialRuntimeEncoder]
  rw [hm, he]
  exact hc.symm

theorem finalRuntimeEncoder_eq_released (m : FinalMessage WideExact) :
    finalRuntimeEncoder m =
      AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m := by
  funext i
  have hp := finalRuntimePoint_eq_conversion i
  have hm : (1 : WideExact) = finalConversion.multipliers i := by
    simp [finalConversion, AspisWide.GRSConversion.exactFinalGRSConversion]
  have he : CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) =
      (finalConversion.messagePolynomial m).eval (finalConversion.points i) := by
    rw [CPolynomial.eval_toPoly,
      AspisWide.GSActualEncoderGRSBridge.final_encode_to_grs_messagePolynomial,
      hp]
  have hc := finalConversion.coordinate_identity m i
  change AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m i =
      finalConversion.multipliers i *
        (finalConversion.messagePolynomial m).eval (finalConversion.points i) at hc
  dsimp [finalRuntimeEncoder]
  calc
    CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) =
        1 * CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) := by simp
    _ = finalConversion.multipliers i *
        (finalConversion.messagePolynomial m).eval (finalConversion.points i) := by
          rw [hm, he]
    _ = AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m i := hc.symm

/-- These close predicates are executable: they use only the literal
CPolynomial evaluators above and finite agreement counting. -/
def initialRuntimeCloseAtLeast (received : InitialWord WideExact)
    (m : InitialMessage WideExact) : Prop :=
  closeAtLeast 38230 initialRuntimeEncoder received m

def finalRuntimeCloseAtLeast (received : FinalWord WideExact)
    (m : FinalMessage WideExact) : Prop :=
  closeAtLeast 9558 finalRuntimeEncoder received m

/-- Executable distance-filter lists. They preserve the raw candidate order
and use no Finset-toList or noncomputable polynomial encoder. -/
def initialRuntimeCloseList (received : InitialWord WideExact)
    (candidates : List (List WideExact)) : List (InitialMessage WideExact) :=
  (AspisWide.GSInitialMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (initialRuntimeCloseAtLeast received m))

def finalRuntimeCloseList (received : FinalWord WideExact)
    (candidates : List (List WideExact)) : List (FinalMessage WideExact) :=
  (AspisWide.GSFinalMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (finalRuntimeCloseAtLeast received m))

theorem initialRuntimeClose_iff_exact (received : InitialWord WideExact)
    (m : InitialMessage WideExact) :
    initialRuntimeCloseAtLeast received m ↔
      closeAtLeast 38230
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
        received m := by
  simp [initialRuntimeCloseAtLeast, initialRuntimeEncoder_eq_released]

theorem finalRuntimeClose_iff_exact (received : FinalWord WideExact)
    (m : FinalMessage WideExact) :
    finalRuntimeCloseAtLeast received m ↔
      closeAtLeast 9558
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
        received m := by
  simp [finalRuntimeCloseAtLeast, finalRuntimeEncoder_eq_released]

theorem initialRuntimeCloseList_mem_iff (received : InitialWord WideExact)
    (candidates : List (List WideExact)) (m : InitialMessage WideExact) :
    m ∈ initialRuntimeCloseList received candidates ↔
      m ∈ AspisWide.GSInitialMessageCandidateFilter.filterCandidates candidates ∧
        closeAtLeast 38230
          (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
          received m := by
  simp [initialRuntimeCloseList, initialRuntimeCloseAtLeast,
    initialRuntimeEncoder_eq_released]

theorem finalRuntimeCloseList_mem_iff (received : FinalWord WideExact)
    (candidates : List (List WideExact)) (m : FinalMessage WideExact) :
    m ∈ finalRuntimeCloseList received candidates ↔
      m ∈ AspisWide.GSFinalMessageCandidateFilter.filterCandidates candidates ∧
        closeAtLeast 9558
          (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
          received m := by
  simp [finalRuntimeCloseList, finalRuntimeCloseAtLeast,
    finalRuntimeEncoder_eq_released]

#print axioms initialRuntimePoint
#print axioms finalRuntimePoint
#print axioms initialRuntimeEncoder
#print axioms finalRuntimeEncoder
#print axioms initialRuntimeEncoder_eq_released
#print axioms finalRuntimeEncoder_eq_released
#print axioms initialRuntimeCloseList
#print axioms finalRuntimeCloseList
#print axioms initialRuntimeClose_iff_exact
#print axioms finalRuntimeClose_iff_exact
#print axioms initialRuntimeCloseList_mem_iff
#print axioms finalRuntimeCloseList_mem_iff

end AspisWide.GSRuntimeDistanceEncoderBridge
