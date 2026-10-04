import AspisV8R19.R607FieldSetMass
import AspisV8R19.R603CircleAcceptanceSet
import AspisV8R19.SamplerCirclePolicy

set_option autoImplicit false
set_option maxRecDepth 4096
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
    · simp [hsing, SamplerCirclePolicy.pureMap]
    · simp [hsing, him, SamplerCirclePolicy.pureMap]

def rejectedTuples : Finset (Fin 4 → Fin modulus) :=
  Finset.univ.filter (fun x => (tupleField x).im = 0)

theorem rejected_tuple_count : rejectedTuples.card = modulus^2 := by
  classical
  have haccepted : (Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
      ∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q)).card =
        modulus^4 - modulus^2 :=
    R603CircleAcceptanceSet.accepted_tuple_count
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4 → Fin modulus)))
    (p := fun x => (tupleField x).im ≠ 0)
  have hreject : Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
      ¬ (tupleField x).im ≠ 0) = rejectedTuples := by
    ext x
    simp [rejectedTuples]
  have haccept : Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
      (tupleField x).im ≠ 0) =
      Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
        ∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (R603CircleAcceptanceSet.tuple_im_nonzero_iff x).trans
      (R603CircleAcceptanceSet.pureMap_success_iff x).symm
  rw [hreject, haccept, haccepted, Finset.card_univ] at hsplit
  simp only [Fintype.card_fun, Fintype.card_fin] at hsplit
  have hp2 : 1 ≤ modulus^2 := by norm_num [modulus]
  have hpow : modulus^2 ≤ modulus^4 := by
    calc
      modulus^2 = modulus^2 * 1 := by simp
      _ ≤ modulus^2 * modulus^2 := Nat.mul_le_mul_left _ hp2
      _ = modulus^4 := by rw [← pow_add]; norm_num
  have hnonneg : 0 ≤ modulus^2 := Nat.zero_le _
  have hmul : modulus^2 ≤ modulus^4 := hpow
  omega

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
            exact (Finset.mem_filter.mp hx).2
          exact accept_none_iff xs |>.mpr him
        · intro hnone
          have him := (accept_none_iff xs).mp hnone
          let x : Fin 4 → Fin modulus :=
            tupleFieldEquiv.symm (SamplerFieldDecode.decode xs)
          have hxval : tupleField x = SamplerFieldDecode.decode xs :=
            tupleFieldEquiv.apply_symm_apply _
          refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hxval.symm⟩
          rw [← hxval]
          exact him
      change (if ∃ x ∈ rejectedTuples,
          SamplerFieldDecode.decode xs = tupleField x then (1 : ℚ) else 0) = _
      rw [hevent]
      simp
end

#print axioms accept_point_iff
#print axioms accept_none_iff
#print axioms rejected_tuple_count
#print axioms rejected_event_eq
end
end AspisV8R19.R608CircleOutcomeEvents
