import M31WideExactPacking
import M31EightLimbAbortBound

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

/-- The finite predicate used by the eight-block decoder: every 16-word
block must have an accepted output under the actual retry decoder. -/
abbrev AllEightAccepted (xs : EightRetryInputs) : Prop :=
  ∀ i : Fin 8, ∃ r : Value, output decode31 (xs i) = some r

/-- Executable all-success test: check the eight `Option` tags directly,
without deciding a large existential by enumerating the field. -/
abbrev AllEightReturned (xs : EightRetryInputs) : Prop :=
  ∀ i : Fin 8, output decode31 (xs i) ≠ none

theorem allEightReturned_iff_accepted (xs : EightRetryInputs) :
    AllEightReturned xs ↔ AllEightAccepted xs := by
  constructor
  · intro h i
    cases hout : output decode31 (xs i) with
    | none => exact False.elim (h i hout)
    | some r => exact ⟨r, rfl⟩
  · intro h i hnone
    obtain ⟨r, hr⟩ := h i
    rw [hnone] at hr
    cases hr

/-- The candidate decoder checks all eight outputs and returns their values.
`canonicalOutput` is only observed on the successful branch, where the exact
output equation below identifies it with the accepted value. -/
def decodeEight (xs : EightRetryInputs) : Option EightValues :=
  if h : AllEightReturned xs then
    some (fun i => canonicalOutput (xs i))
  else none

theorem canonicalOutput_success (xs : RetryInput)
    (h : ∃ r : Value, output decode31 xs = some r) :
    output decode31 xs = some (canonicalOutput xs) := by
  obtain ⟨r, hr⟩ := h
  simp [canonicalOutput, hr]

theorem decodeEight_some_iff (xs : EightRetryInputs) (ys : EightValues) :
    decodeEight xs = some ys ↔
      AllEightReturned xs ∧ ys = fun i => canonicalOutput (xs i) := by
  unfold decodeEight
  by_cases h : AllEightReturned xs
  · simp only [dif_pos h, Option.some.injEq]
    constructor
    · intro heq
      exact ⟨h, heq.symm⟩
    · intro hh
      exact hh.2.symm
  · simp [h]

theorem decodeEight_readback (xs : EightRetryInputs)
    (h : AllEightAccepted xs) (i : Fin 8) :
    output decode31 (xs i) = some ((fun j => canonicalOutput (xs j)) i) :=
  canonicalOutput_success (xs i) (h i)

/-- Apply the proved retained-field packing to the successful eight-value
decode. This is a concrete total function on the complete finite input tape. -/
def actualEightWideSampler (xs : EightRetryInputs) : Option WideExactOutput :=
  (decodeEight xs).map outputToWideExact

/-- The actual sampler's output fiber, expressed as an input subtype. -/
abbrev actualWideOutputFiber (w : WideExactOutput) :=
  {xs : EightRetryInputs // actualEightWideSampler xs = some w}

theorem actualEightWideSampler_none_iff (xs : EightRetryInputs) :
    actualEightWideSampler xs = none ↔ ¬ AllEightAccepted xs := by
  have hret : actualEightWideSampler xs = none ↔ ¬ AllEightReturned xs := by
    unfold actualEightWideSampler decodeEight
    by_cases h : AllEightReturned xs <;> simp [h]
  exact hret.trans (not_congr (allEightReturned_iff_accepted xs))

theorem actualEightWideSampler_some_iff (xs : EightRetryInputs)
    (w : WideExactOutput) :
    actualEightWideSampler xs = some w ↔
      ∃ ys : EightValues, AllEightAccepted xs ∧
        ys = (fun i => canonicalOutput (xs i)) ∧ outputToWideExact ys = w := by
  unfold actualEightWideSampler
  cases h : decodeEight xs with
  | none =>
      constructor
      · simp [h]
      · rintro ⟨ys, hall, hys, hout⟩
        have hret := (allEightReturned_iff_accepted xs).mpr hall
        have hsome : decodeEight xs = some (fun i => canonicalOutput (xs i)) := by
          simp [decodeEight, hret]
        rw [h] at hsome
        cases hsome
  | some ys =>
      have hdec := (decodeEight_some_iff xs ys).mp h
      constructor
      · intro hout
        have hout' : outputToWideExact ys = w := by simpa using hout
        exact ⟨ys, (allEightReturned_iff_accepted xs).mp hdec.1,
          hdec.2, hout'⟩
      · rintro ⟨zs, hall, hzs, hout⟩
        have hzsYs : zs = ys := hzs.trans hdec.2.symm
        rw [hzsYs] at hout
        have hout' : outputToWideExact ys = w := hout
        simpa [h] using hout'

/-- A successful input producing `w` is exactly an element of the previously
counted product fiber at the inverse packed value. -/
def actualWideOutputFiberEquiv (w : WideExactOutput) :
    actualWideOutputFiber w ≃ wideExactOutputFiber w where
  toFun x := by
    cases hdec : decodeEight x.1 with
    | none =>
        have hx := x.2
        simp [actualEightWideSampler, hdec] at hx
    | some ys =>
      have hprops := (decodeEight_some_iff x.1 ys).mp hdec
      have hall := (allEightReturned_iff_accepted x.1).mp hprops.1
      have hys := hprops.2
      have hout : outputToWideExact ys = w := by
        simpa [actualEightWideSampler, hdec] using x.2
      have hraw : (fun i => canonicalOutput (x.1 i)) = outputToWideExact.symm w := by
        apply outputToWideExact.injective
        calc
          outputToWideExact (fun i => canonicalOutput (x.1 i)) =
              outputToWideExact ys := by rw [← hys]
          _ = w := hout
          _ = outputToWideExact (outputToWideExact.symm w) := by simp
      refine ⟨x.1, ?_⟩
      intro i
      rw [← congrFun hraw i]
      exact canonicalOutput_success (x.1 i) (hall i)
  invFun x := by
    refine ⟨x.1, ?_⟩
    have hall : AllEightAccepted x.1 := by
      intro i
      exact ⟨outputToWideExact.symm w i, x.2 i⟩
    have hraw : (fun i => canonicalOutput (x.1 i)) = outputToWideExact.symm w := by
      funext i
      have hcan := canonicalOutput_success (x.1 i) ⟨_, x.2 i⟩
      exact Option.some.inj (hcan.symm.trans (x.2 i))
    have hreturned := (allEightReturned_iff_accepted x.1).mpr hall
    have hdecode : decodeEight x.1 = some (outputToWideExact.symm w) := by
      simp [decodeEight, hreturned, hraw]
    change actualEightWideSampler x.1 = some w
    simp [actualEightWideSampler, hdecode]
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem actualWideOutputFiber_card (w : WideExactOutput) :
    Nat.card (actualWideOutputFiber w) = limbBaseCount ^ 8 := by
  calc
    Nat.card (actualWideOutputFiber w) = Nat.card (wideExactOutputFiber w) :=
      Nat.card_congr (actualWideOutputFiberEquiv w)
    _ = limbBaseCount ^ 8 := wideExactOutputFiber_card w

theorem actualWideConditionalMass_uniform (w : WideExactOutput) :
    (Nat.card (actualWideOutputFiber w) : ℚ) /
      (Nat.card EightSuccessInput : ℚ) = 1 / (P31 : ℚ) ^ 8 := by
  have h := wideExactConditionalMass_uniform w
  unfold wideExactConditionalMass eightConditionalMass at h
  have hcard : Nat.card (eightOutputFiber (outputToWideExact.symm w)) = limbBaseCount ^ 8 :=
    wideExactOutputFiber_card w
  rw [hcard] at h
  rw [actualWideOutputFiber_card]
  exact h

theorem actualWideSampler_abort_iff (xs : EightRetryInputs) :
    actualEightWideSampler xs = none ↔ ¬ EightSuccessProp xs := by
  change actualEightWideSampler xs = none ↔ ¬ AllEightAccepted xs
  exact actualEightWideSampler_none_iff xs

abbrev actualWideAbortInput :=
  {xs : EightRetryInputs // actualEightWideSampler xs = none}

def actualWideAbortInputEquiv : actualWideAbortInput ≃ EightAbortInput where
  toFun x := ⟨x.1, actualWideSampler_abort_iff x.1 |>.mp x.2⟩
  invFun x := ⟨x.1, actualWideSampler_abort_iff x.1 |>.mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem actualWideAbortInput_card :
    Nat.card actualWideAbortInput = Nat.card EightAbortInput :=
  Nat.card_congr actualWideAbortInputEquiv

noncomputable def actualWideAbortMass : ℚ :=
  (Nat.card actualWideAbortInput : ℚ) / (Nat.card EightRetryInputs : ℚ)

theorem actualWideAbortMass_eq_eightAbortMass :
    actualWideAbortMass = eightAbortMass := by
  unfold actualWideAbortMass eightAbortMass
  rw [actualWideAbortInput_card]

theorem actualWideAbortMass_exact :
    actualWideAbortMass = 1 - (1 - (1 : ℚ) / (2 : ℚ) ^ 496) ^ 8 := by
  rw [actualWideAbortMass_eq_eightAbortMass, eightAbortMass_exact]

#print axioms canonicalOutput_success
#print axioms decodeEight_some_iff
#print axioms actualEightWideSampler_none_iff
#print axioms actualWideOutputFiberEquiv
#print axioms actualWideOutputFiber_card
#print axioms actualWideConditionalMass_uniform
#print axioms actualWideSampler_abort_iff
#print axioms actualWideAbortInputEquiv
#print axioms actualWideAbortInput_card
#print axioms actualWideAbortMass_exact

end M31RetryOutputFiber
