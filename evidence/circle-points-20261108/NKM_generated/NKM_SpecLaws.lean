import NKM_Domains
set_option autoImplicit false
noncomputable section
namespace NKM_SpecLaws
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_circle NKM_FieldLaws

def decode (q : NKM_circle.field.QM31) : QM31Exact := SamplerClosureProductCorrectness.decode (toQ q)
def product (a b : NKM_circle.field.QM31) : NKM_circle.field.QM31 := encode (decode a * decode b)
def addition (a b : NKM_circle.field.QM31) : NKM_circle.field.QM31 := encode (decode a + decode b)
def subtraction (a b : NKM_circle.field.QM31) : NKM_circle.field.QM31 := encode (decode a - decode b)
def inverse (a : NKM_circle.field.QM31) : Option NKM_circle.field.QM31 :=
 if decode a=0 then none else some (encode (decode a)⁻¹)

theorem product_law (a b : NKM_circle.field.QM31) (ha : Canon a) (hb : Canon b) :
 NKM_circle.field.QM31.mul a b = ok (product a b) := by
 conv_lhs => rw [←roundtrip a ha,←roundtrip b hb]
 exact mul _ _

theorem square_law (a : NKM_circle.field.QM31) (ha : Canon a) :
 NKM_circle.field.QM31.square a = ok (product a a) := by
 conv_lhs => rw [←roundtrip a ha]
 exact square _

theorem add_law (a b : NKM_circle.field.QM31) (ha : Canon a) (hb : Canon b) :
 NKM_circle.field.QM31.add a b = ok (addition a b) := by
 conv_lhs => rw [←roundtrip a ha,←roundtrip b hb]
 exact add _ _

theorem sub_law (a b : NKM_circle.field.QM31) (ha : Canon a) (hb : Canon b) :
 NKM_circle.field.QM31.sub a b = ok (subtraction a b) := by
 conv_lhs => rw [←roundtrip a ha,←roundtrip b hb]
 exact sub _ _

theorem inverse_law (a : NKM_circle.field.QM31) (ha : Canon a) :
 NKM_circle.field.QM31.try_inv a = ok (inverse a) := by
 conv_lhs => rw [←roundtrip a ha]
 exact NKM_Domains.inverse_return _

theorem decode_encode (a : QM31Exact) : decode (encode a) = a := by
 unfold decode encode
 rw [to_from]
 exact SamplerClosureProductCorrectness.decode_encode a

/-- Canonical natural inverse spec: None exactly on zero, otherwise a canonical multiplicative inverse. -/
def inverseRel (a : NKM_circle.field.QM31) (r : Option NKM_circle.field.QM31) : Prop :=
 match r with
 | none => decode a=0
 | some b => Canon b ∧ decode a * decode b=1

theorem inverse_spec (a : NKM_circle.field.QM31) : inverseRel a (inverse a) := by
 by_cases hz:decode a=0
 · simp only [inverse,hz,if_true,inverseRel]
 · simp only [inverse,hz,if_false,inverseRel,decode_encode]
   exact ⟨canonical _,mul_inv_cancel₀ hz⟩

theorem inverse_unique (a : NKM_circle.field.QM31) (r : Option NKM_circle.field.QM31)
 (h : inverseRel a r) : r=inverse a := by
 cases r with
 | none => simp only [inverseRel] at h; simp only [inverse,h,if_true]
 | some b =>
  rcases h with ⟨hb,hm⟩
  have hz : decode a≠0 := by intro hz;rw [hz,zero_mul] at hm;exact zero_ne_one hm
  have hi : decode b=(decode a)⁻¹ := by
   calc
    decode b = 1*decode b := (one_mul _).symm
    _ = ((decode a)⁻¹*decode a)*decode b := by rw [inv_mul_cancel₀ hz]
    _ = (decode a)⁻¹ := by rw [mul_assoc,hm,mul_one]
  simp only [inverse,hz,if_false]
  congr 1
  rw [←hi]
  exact (roundtrip b hb).symm

#print axioms product_law
#print axioms square_law
#print axioms add_law
#print axioms sub_law
#print axioms inverse_law
#print axioms decode_encode
#print axioms inverse_spec
#print axioms inverse_unique
end NKM_SpecLaws
end
