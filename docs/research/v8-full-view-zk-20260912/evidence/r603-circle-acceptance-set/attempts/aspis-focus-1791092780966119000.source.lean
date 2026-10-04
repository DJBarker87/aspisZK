import AspisV8R19.R599CanonicalFieldTuple
import AspisV8R19.R602CircleParameterCount
import AspisV8R19.SamplerCirclePolicy

set_option autoImplicit false
namespace AspisV8R19.R603CircleAcceptanceSet
open AspisV8R15.ExactTowerBase
open AspisV8R19.R445InitialBlockRejectionLaw (modulus)
open AspisV8R19.R599CanonicalFieldTuple
open AspisV8R19.R602CircleParameterCount
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerFieldDecode (decode4 decode4_im_zero)
noncomputable section

def selectedZero : Fin modulus := ⟨0, by norm_num [modulus]⟩

theorem fin_val_zero_iff (x : Fin modulus) : x.val = 0 ↔ x = selectedZero := by
  constructor
  · intro h
    apply Fin.ext
    simpa [selectedZero] using h
  · intro h
    simpa [selectedZero] using congrArg Fin.val h

theorem tuple_im_nonzero_iff (x : Fin 4 → Fin modulus) :
    (tupleField x).im ≠ 0 ↔ x 2 ≠ selectedZero ∨ x 3 ≠ selectedZero := by
  have hdecode := decode4_im_zero (x 0).val (x 1).val (x 2).val (x 3).val
    (x 2).isLt (x 3).isLt
  change (decode4 (x 0).val (x 1).val (x 2).val (x 3).val).im ≠ 0 ↔ _
  rw [hdecode]
  rw [not_and_or, fin_val_zero_iff (x 2), fin_val_zero_iff (x 3)]

theorem pureMap_success_iff (x : Fin 4 → Fin modulus) :
    (∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q) ↔
      x 2 ≠ selectedZero ∨ x 3 ≠ selectedZero := by
  constructor
  · rintro ⟨q,hq⟩
    exact tuple_im_nonzero_iff x |>.mp (SamplerCirclePolicy.success_policy _ q hq).1
  · intro h
    have hi := tuple_im_nonzero_iff x |>.mpr h
    exact ⟨SamplerCirclePolicy.point (tupleField x),
      SamplerCirclePolicy.outside_map (tupleField x) hi⟩

noncomputable instance acceptedDecidable : DecidablePred
    (fun x : Fin 4 → Fin modulus =>
      ∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q) := by
  intro x
  exact Classical.propDecidable _

theorem accepted_tuple_count :
    (Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
      ∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q)).card =
        modulus^4 - modulus^2 := by
  classical
  have hfilter : Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
      ∃ q, SamplerCirclePolicy.pureMap (tupleField x) = Except.ok q) =
      Finset.univ.filter (fun x : Fin 4 → Fin modulus =>
        x 2 ≠ selectedZero ∨ x 3 ≠ selectedZero) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact pureMap_success_iff x
  rw [hfilter]
  simpa [selectedZero] using
    (R602CircleParameterCount.circle_parameter_count modulus
      (by norm_num [modulus]))

#print axioms fin_val_zero_iff
#print axioms tuple_im_nonzero_iff
#print axioms pureMap_success_iff
#print axioms accepted_tuple_count
end
end AspisV8R19.R603CircleAcceptanceSet
