import NKM_NaturalLaws
set_option autoImplicit false
noncomputable section
namespace NKM_SpecMatching
open AspisV8R15.ExactTowerBase
open NKM_FieldLaws NKM_SpecLaws

theorem decode_zero_iff (a : NKM_circle.field.QM31) (ha : Canon a) :
 decode a=0 ↔ a=NKM_circle.field.QM31.ZERO := by
 constructor
 · intro h
   calc
    a=encode (decode a) := (roundtrip a ha).symm
    _=NKM_circle.field.QM31.ZERO := by rw [h,←zero]
 · intro h
   rw [h,zero,decode_encode]

theorem product_one_iff (a b : NKM_circle.field.QM31) :
 product a b=NKM_circle.field.QM31.ONE ↔ decode a*decode b=1 := by
 constructor
 · intro h
   have hd := congrArg decode h
   simpa only [product,decode_encode,one] using hd
 · intro h
   unfold product
   rw [h,←one]

theorem product_canonical (a b : NKM_circle.field.QM31) : Canon (product a b) := canonical _

/-- Exact connection of the native inverse assume clauses, including raw zero and ONE. -/
theorem native_inverse_relation (a : NKM_circle.field.QM31) (ha : Canon a)
 (r : Option NKM_circle.field.QM31) :
 (match r with
 | none => a=NKM_circle.field.QM31.ZERO
 | some b => Canon b ∧ product a b=NKM_circle.field.QM31.ONE) ↔ inverseRel a r := by
 cases r with
 | none => exact (decode_zero_iff a ha).symm
 | some b => exact and_congr_right (fun _ => product_one_iff a b)

#print axioms decode_zero_iff
#print axioms product_one_iff
#print axioms product_canonical
#print axioms native_inverse_relation
end NKM_SpecMatching
end
