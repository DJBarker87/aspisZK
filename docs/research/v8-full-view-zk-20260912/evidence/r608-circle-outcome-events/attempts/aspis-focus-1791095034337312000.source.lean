import AspisV8R19.R607FieldSetMass
import AspisV8R19.R603CircleAcceptanceSet
import AspisV8R19.SamplerCirclePolicy
import Mathlib.Data.Fin.VecNotation

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
    · simp [hsing, Except.toOption]
    · simp [hsing, him, Except.toOption]

@[implicit_reducible] noncomputable def selectedTupleFintype :
    Fintype R607FieldSetMass.Tuple := inferInstance
local instance : Fintype R607FieldSetMass.Tuple := selectedTupleFintype
local instance : DecidableEq R607FieldSetMass.Tuple := Classical.decEq _
local instance : DecidablePred
    (fun x : R607FieldSetMass.Tuple => x 2 = 0 ∧ x 3 = 0) := by
  intro x
  exact Classical.propDecidable _

noncomputable def rejectedTuples : Finset R607FieldSetMass.Tuple := by
  exact Finset.univ.filter (fun x => x 2 = 0 ∧ x 3 = 0)

theorem mem_rejectedTuples_iff (x : R607FieldSetMass.Tuple) :
    x ∈ rejectedTuples ↔ x 2 = 0 ∧ x 3 = 0 := by
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hcoord
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcoord⟩

theorem rejected_tuple_count : rejectedTuples.card = modulus^2 := by
  classical
  let z : Fin modulus := R603CircleAcceptanceSet.selectedZero
  have heq : Fintype.card rejectedTuples = Fintype.card (Fin 2 → Fin modulus) := by
    simpa [rejectedTuples, z, R603CircleAcceptanceSet.selectedZero_eq_zero] using
      Fintype.card_congr
        (AspisV8R19.R602CircleParameterCount.fixedTailEquiv z)
  have hcard : rejectedTuples.card = Fintype.card rejectedTuples :=
    (Fintype.card_coe rejectedTuples).symm
  rw [hcard, heq]
  simp

theorem rejected_event_eq (out : Option (List Nat)) :
    R607FieldSetMass.setEvent rejectedTuples out =
      (if ∃ xs, out = some xs ∧ SamplerCirclePolicy.accept xs = none
        then (1 : ℚ) else 0) := by
  cases out with
  | none => simp [R607FieldSetMass.setEvent]
  | some xs =>
      have hevent : (∃ x : R607FieldSetMass.Tuple,
          x ∈ rejectedTuples ∧
          SamplerFieldDecode.decode xs = tupleField x) ↔
          SamplerCirclePolicy.accept xs = none := by
        constructor
        · rintro ⟨(x : Fin 4 → Fin modulus),hx,hdecode⟩
          have him : (SamplerFieldDecode.decode xs).im = 0 := by
            have hcoords := (mem_rejectedTuples_iff x).mp hx
            have hnot : ¬ (x 2 ≠ 0 ∨ x 3 ≠ 0) := by
              simp [hcoords.1, hcoords.2]
            have himnot :=
              (not_congr (R603CircleAcceptanceSet.tuple_im_nonzero_iff x)).mpr hnot
            exact (congrArg (fun q : QM31Exact => q.im) hdecode).trans
              (not_ne_iff.mp himnot)
          exact accept_none_iff xs |>.mpr him
        · intro hnone
          have him := (accept_none_iff xs).mp hnone
          let x : Fin 4 → Fin modulus :=
            tupleFieldEquiv.symm (SamplerFieldDecode.decode xs)
          have hxval : tupleField x = SamplerFieldDecode.decode xs :=
            (R599CanonicalFieldTuple.tupleFieldEquiv_apply x).symm.trans
              (tupleFieldEquiv.apply_symm_apply _)
          have himx : (tupleField x).im = 0 :=
            (congrArg (fun q : QM31Exact => q.im) hxval).trans him
          have hnot : ¬ ((tupleField x).im ≠ 0) := by simpa [himx]
          have hcoords :=
            (not_congr (R603CircleAcceptanceSet.tuple_im_nonzero_iff x)).mp hnot
          have hcoords' : x 2 = 0 ∧ x 3 = 0 := by simpa using hcoords
          have hxmem : x ∈ rejectedTuples :=
            (mem_rejectedTuples_iff x).mpr hcoords'
          exact ⟨x, hxmem, hxval.symm⟩
      simp [R607FieldSetMass.setEvent, hevent]
end

#print axioms accept_point_iff
#print axioms accept_none_iff
#print axioms rejected_tuple_count
#print axioms rejected_event_eq
end AspisV8R19.R608CircleOutcomeEvents
