import AspisV8R19.R607FieldSetMass
import AspisV8R19.R603CircleAcceptanceSet
import AspisV8R19.SamplerCirclePolicy

set_option autoImplicit false
set_option maxRecDepth 16384
namespace AspisV8R19.R608CircleOutcomeEvents
open AspisV8R15.ExactTowerBase
open AspisV8R19.R445InitialBlockRejectionLaw (modulus)
open AspisV8R19.R599CanonicalFieldTuple
open AspisV8R19.R603CircleAcceptanceSet
open AspisV8R19.SamplerCirclePolicy
noncomputable section

theorem accept_point_iff (xs : List Nat) (a : QM31Exact) (ha : a.im ≠ 0) :
    SamplerCirclePolicy.accept xs = some (SamplerCirclePolicy.point a) ↔
      SamplerFieldDecode.decode xs = a := by
  constructor
  · intro h
    obtain ⟨hi, hd, hpoint⟩ := SamplerCirclePolicy.accept_policy xs _ h
    have heq := SamplerCirclePolicy.point_injective a
      (SamplerFieldDecode.decode xs)
      (SamplerCirclePolicy.outside_has_denominator a ha) hd hpoint
    exact heq.symm
  · intro hdecode
    unfold SamplerCirclePolicy.accept
    rw [hdecode]
    rw [SamplerCirclePolicy.outside_map a ha]
    rfl

theorem accept_none_iff (xs : List Nat) :
    SamplerCirclePolicy.accept xs = none ↔
      (SamplerFieldDecode.decode xs).im = 0 := by
  constructor
  · intro hnone
    by_contra him
    have hout := SamplerCirclePolicy.outside_map (SamplerFieldDecode.decode xs) him
    unfold SamplerCirclePolicy.accept at hnone
    rw [hout] at hnone
    cases hnone
  · intro him
    unfold SamplerCirclePolicy.accept SamplerCirclePolicy.pureMap
    by_cases hsing : 1 + (SamplerFieldDecode.decode xs)^2 = 0
    · simp [hsing, Except.toOption]
    · simp [hsing, him, Except.toOption]

def rejectedTuples : Finset (Fin 4 → Fin modulus) :=
  Finset.univ.filter (fun x => (tupleField x).im = 0)

theorem rejected_tuple_count : rejectedTuples.card = modulus^2 := by
  classical
  let z : Fin modulus := R603CircleAcceptanceSet.selectedZero
  let bad : Finset (Fin 4 → Fin modulus) :=
    Finset.univ.filter (fun x => x 2 = z ∧ x 3 = z)
  have hbad : bad.card = modulus^2 := by
    have heq : Fintype.card bad = Fintype.card (Fin 2 → Fin modulus) := by
      simpa [bad] using Fintype.card_congr
        (AspisV8R19.R602CircleParameterCount.fixedTailEquiv z)
    have hcard : bad.card = Fintype.card bad := (Fintype.card_coe bad).symm
    rw [hcard, heq]
    simp
  have hreject : rejectedTuples = bad := by
    ext x
    simp only [rejectedTuples, bad, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro him
      have hn : ¬ ((tupleField x).im ≠ 0) := by simpa [him]
      have hcoord := (not_congr (R603CircleAcceptanceSet.tuple_im_nonzero_iff x)).mp hn
      have hcoord' : x 2 = 0 ∧ x 3 = 0 := by simpa using hcoord
      simpa [z, R603CircleAcceptanceSet.selectedZero_eq_zero] using hcoord'
    · rintro ⟨h2,h3⟩
      have h2' : x 2 = 0 := by simpa [z, R603CircleAcceptanceSet.selectedZero_eq_zero] using h2
      have h3' : x 3 = 0 := by simpa [z, R603CircleAcceptanceSet.selectedZero_eq_zero] using h3
      have hn : ¬ (x 2 ≠ 0 ∨ x 3 ≠ 0) := by simp [h2', h3']
      have himn := (not_congr (R603CircleAcceptanceSet.tuple_im_nonzero_iff x)).mpr hn
      exact not_ne_iff.mp himn
  rw [hreject, hbad]

theorem rejected_event_eq (out : Option (List Nat)) :
    R607FieldSetMass.setEvent rejectedTuples out =
      (if ∃ xs, out = some xs ∧ SamplerCirclePolicy.accept xs = none
        then (1 : ℚ) else 0) := by
  classical
  cases out with
  | none => simp [R607FieldSetMass.setEvent]
  | some xs =>
      have hevent : (∃ x ∈ rejectedTuples,
          SamplerFieldDecode.decode xs = tupleField x) ↔
          SamplerCirclePolicy.accept xs = none := by
        constructor
        · rintro ⟨x,hx,hdecode⟩
          have him : (SamplerFieldDecode.decode xs).im = 0 := by
            rw [hdecode]
            change (tupleField x).im = 0 at hx
            exact hx
          exact accept_none_iff xs |>.mpr him
        · intro hnone
          have him := (accept_none_iff xs).mp hnone
          let x : Fin 4 → Fin modulus :=
            tupleFieldEquiv.symm (SamplerFieldDecode.decode xs)
          have hxval : tupleField x = SamplerFieldDecode.decode xs :=
            tupleFieldEquiv.apply_symm_apply _
          refine ⟨x, ?_, hxval.symm⟩
          change (tupleField x).im = 0
          rw [← hxval]
          exact him
      simp [R607FieldSetMass.setEvent, hevent]
end

#print axioms accept_point_iff
#print axioms accept_none_iff
#print axioms rejected_tuple_count
#print axioms rejected_event_eq
end AspisV8R19.R608CircleOutcomeEvents
