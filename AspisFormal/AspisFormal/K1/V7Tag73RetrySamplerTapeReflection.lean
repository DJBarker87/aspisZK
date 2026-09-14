import AspisFormal.K1.V7Tag73FiniteTapeLaw
import AspisFormal.K1.V7Tag73StoppedSamplerKernel

/-!
# Actual finite-tape semantics of the generic bounded-retry decoder

This closes the gap between a recurrence CALLED first-success mass and the
probability of a real recursive Option-valued sampler on the explicit iid law.
The production sampler must still be proved to implement this exact control
flow (or its appropriate multi-block generalization). No such source identity
is assumed or claimed here.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73RetrySamplerTapeReflection
open MeasureTheory
open scoped BigOperators
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73FiniteTapeLaw
open AspisK1.V7Tag73FiniteSubkernel
open AspisK1.V7Tag73StoppedSamplerKernel
noncomputable section
variable {Raw : Type} [Fintype Raw] [Nonempty Raw]
variable {Value : Type*} [DecidableEq Value]

/-- Return the first successful decode, consuming at most the supplied tape. -/
def firstDecoded (decode : Raw → Option Value) :
    (n : Nat) → FreshAnswerTape Raw n → Option Value
  | 0, _ => none
  | n + 1, tape => match decode tape.1 with
    | some value => some value
    | none => firstDecoded decode n tape.2

theorem firstDecoded_stops_at_success (decode : Raw → Option Value)
    (n : Nat) (head : Raw) (value : Value) (tail : FreshAnswerTape Raw n)
    (success : decode head = some value) :
    firstDecoded decode (n+1) (head,tail) = some value := by
  simp [firstDecoded, success]

/-- Exact first-step atom equation, including all rejecting first draws. -/
theorem firstDecoded_atom_succ (law : PMF Raw) (decode : Raw → Option Value)
    (value : Value) (n : Nat) :
    (iidTape law (n+1)).toOuterMeasure
        {t | firstDecoded decode (n+1) t = some value} =
      decodedAtomMass law decode value + rejectMass law decode *
        (iidTape law n).toOuterMeasure {t | firstDecoded decode n t = some value} := by
  classical
  rw [iidTape_event_succ]
  unfold decodedAtomMass rejectMass eventMass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro raw _
  cases hd : decode raw with
  | none => simp [firstDecoded, hd]
  | some found =>
      by_cases same : found = value <;> simp [firstDecoded, hd, same]

/-- Exact first-step exhaustion equation; failed decodes are not conditioned away. -/
theorem firstDecoded_none_succ (law : PMF Raw) (decode : Raw → Option Value)
    (n : Nat) :
    (iidTape law (n+1)).toOuterMeasure
        {t | firstDecoded decode (n+1) t = none} =
      rejectMass law decode *
        (iidTape law n).toOuterMeasure {t | firstDecoded decode n t = none} := by
  classical
  rw [iidTape_event_succ]
  unfold rejectMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro raw _
  cases hd : decode raw <;> simp [firstDecoded, hd]

/-- The previous algebraic recurrence is the probability of this sampler. -/
theorem firstDecoded_atom_mass (law : PMF Raw) (decode : Raw → Option Value)
    (value : Value) (n : Nat) :
    (iidTape law n).toOuterMeasure {t | firstDecoded decode n t = some value} =
      firstSuccessAtom law decode value n := by
  induction n with
  | zero => simp [firstDecoded, firstSuccessAtom]
  | succ n ih => rw [firstDecoded_atom_succ, ih]; rfl

/-- Exhaustion is retained with its exact probability at every finite cap. -/
theorem firstDecoded_exhaustion_mass (law : PMF Raw) (decode : Raw → Option Value)
    (n : Nat) :
    (iidTape law n).toOuterMeasure {t | firstDecoded decode n t = none} =
      exhaustionMass law decode n := by
  induction n with
  | zero => simp [firstDecoded, exhaustionMass]
  | succ n ih => rw [firstDecoded_none_succ, ih]; rfl

/-- Exact law-to-geometric form, with no post-acceptance renormalization. -/
theorem firstDecoded_atom_geometric (law : PMF Raw) (decode : Raw → Option Value)
    (value : Value) (n : Nat) :
    (iidTape law n).toOuterMeasure {t | firstDecoded decode n t = some value} =
      decodedAtomMass law decode value * geometricWeight (rejectMass law decode) n := by
  rw [firstDecoded_atom_mass, firstSuccessAtom_factor]

/-- A finite target decomposes into disjoint returned-value atoms. -/
theorem firstDecoded_target_mass (law : PMF Raw) (decode : Raw → Option Value)
    (target : Finset Value) (n : Nat) :
    (iidTape law n).toOuterMeasure
      {t | ∃ value ∈ target, firstDecoded decode n t = some value} =
      ∑ value ∈ target, firstSuccessAtom law decode value n := by
  rw [pmf_event_eq_eventMass, decoded_bad_mass_eq]
  apply Finset.sum_congr rfl
  intro value _
  change eventMass (iidTape law n)
      (fun t => firstDecoded decode n t = some value) = _
  rw [← pmf_event_eq_eventMass, firstDecoded_atom_mass]

/-- The local kernel bound now applies to the recursive sampler's real event. -/
theorem firstDecoded_target_mass_le (law : PMF Raw) (decode : Raw → Option Value)
    (target : Finset Value) (atomCap : ENNReal)
    (atomBound : ∀ value ∈ target, decodedAtomMass law decode value ≤ atomCap)
    (n : Nat) :
    (iidTape law n).toOuterMeasure
      {t | ∃ value ∈ target, firstDecoded decode n t = some value} ≤
      (target.card : ENNReal) * atomCap * geometricWeight (rejectMass law decode) n := by
  rw [firstDecoded_target_mass]
  calc
    (∑ value ∈ target, firstSuccessAtom law decode value n) =
        (∑ value ∈ target, decodedAtomMass law decode value) *
          geometricWeight (rejectMass law decode) n := by
      simp only [firstSuccessAtom_factor, Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_right'
      calc
        (∑ value ∈ target, decodedAtomMass law decode value) ≤
            ∑ _value ∈ target, atomCap := Finset.sum_le_sum atomBound
        _ = (target.card : ENNReal) * atomCap := by simp [nsmul_eq_mul]

#print axioms firstDecoded_stops_at_success
#print axioms firstDecoded_atom_succ
#print axioms firstDecoded_none_succ
#print axioms firstDecoded_atom_mass
#print axioms firstDecoded_exhaustion_mass
#print axioms firstDecoded_atom_geometric
#print axioms firstDecoded_target_mass
#print axioms firstDecoded_target_mass_le
end
end AspisK1.V7Tag73RetrySamplerTapeReflection
