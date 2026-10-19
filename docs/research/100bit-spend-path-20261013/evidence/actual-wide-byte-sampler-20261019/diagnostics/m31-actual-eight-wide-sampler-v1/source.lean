import M31WideExactPacking
import M31EightLimbAbortBound

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

/-- The finite predicate used by the eight-block decoder: every 16-word
block must have an accepted output under the actual retry decoder. -/
abbrev AllEightAccepted (xs : EightRetryInputs) : Prop :=
  ∀ i : Fin 8, ∃ r : Value, output decode31 (xs i) = some r

/-- The candidate decoder checks all eight outputs and returns their values.
`canonicalOutput` is only observed on the successful branch, where the exact
output equation below identifies it with the accepted value. -/
def decodeEight (xs : EightRetryInputs) : Option EightValues :=
  if h : AllEightAccepted xs then
    some (fun i => canonicalOutput (xs i))
  else none

theorem canonicalOutput_success (xs : RetryInput)
    (h : ∃ r : Value, output decode31 xs = some r) :
    output decode31 xs = some (canonicalOutput xs) := by
  obtain ⟨r, hr⟩ := h
  simp [canonicalOutput, hr]

theorem decodeEight_some_iff (xs : EightRetryInputs) (ys : EightValues) :
    decodeEight xs = some ys ↔
      AllEightAccepted xs ∧ ys = fun i => canonicalOutput (xs i) := by
  unfold decodeEight
  by_cases h : AllEightAccepted xs
  · simp [h]
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
  unfold actualEightWideSampler decodeEight
  by_cases h : AllEightAccepted xs <;> simp [h]

theorem actualEightWideSampler_some_iff (xs : EightRetryInputs)
    (w : WideExactOutput) :
    actualEightWideSampler xs = some w ↔
      ∃ ys : EightValues, AllEightAccepted xs ∧
        ys = (fun i => canonicalOutput (xs i)) ∧ outputToWideExact ys = w := by
  unfold actualEightWideSampler
  cases h : decodeEight xs with
  | none => simp [h]
  | some ys => simp [h, decodeEight_some_iff]

/-- A successful input producing `w` is exactly an element of the previously
counted product fiber at the inverse packed value. -/
def actualWideOutputFiberEquiv (w : WideExactOutput) :
    actualWideOutputFiber w ≃ wideExactOutputFiber w where
  toFun x := by
    have hsome := (actualEightWideSampler_some_iff x.1 w).mp x.2
    rcases hsome with ⟨ys, hall, hys, hout⟩
    have hraw : (fun i => canonicalOutput (x.1 i)) = outputToWideExact.symm w := by
      apply outputToWideExact.injective
      calc
        outputToWideExact (fun i => canonicalOutput (x.1 i)) =
            outputToWideExact ys := by rw [← hys]
        _ = w := hout
        _ = outputToWideExact (outputToWideExact.symm w) := by simp
    refine ⟨x.1, ?_⟩
    intro i
    rw [hraw]
    exact canonicalOutput_success (x.1 i) (hall i)
  invFun x := by
    refine ⟨x.1, ?_⟩
    apply (actualEightWideSampler_some_iff x.1 w).mpr
    refine ⟨outputToWideExact.symm w, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨r, hr⟩ := x.2 i
      exact ⟨r, hr⟩
    · funext i
      have h := canonicalOutput_success (x.1 i) (x.2 i)
      have hval : ((outputToWideExact.symm w) i) =
          canonicalOutput (x.1 i) := by
        apply Option.some.inj
        exact (x.2 i).symm.trans h
      exact hval.symm
    · simp
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
  simpa [actualWideOutputFiber_card] using wideExactConditionalMass_uniform w

theorem actualWideSampler_abort_iff (xs : EightRetryInputs) :
    actualEightWideSampler xs = none ↔ xs ∈ EightAbortInput := by
  rw [actualEightWideSampler_none_iff, abortProp_iff_some_none]

theorem actualWideAbortMass_eq_eightAbortMass :
    (Nat.card EightAbortInput : ℚ) / (Nat.card EightRetryInputs : ℚ) =
      eightAbortMass := rfl

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
