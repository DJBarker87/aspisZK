import XRk_FieldExternal
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Add
-- The exact wrapping-word reference that underlies K020's canonical u64 formula.
def word (a b : U32) : U32 :=
  let sum := U32.wrapping_add a b
  if sum >= 2147483647#u32 then U32.wrapping_sub sum 2147483647#u32 else sum

theorem model_word (a b : U32) : XRk_Field.field.M31.add a b = ok (word a b) := by
  simp only [XRk_Field.field.M31.add, XRk_Field.field.P, word, lift, bind_tc_ok]

def pair (a b : aspis_core.field.CM31) : aspis_core.field.CM31 :=
  ⟨word a.a b.a,word a.b b.b⟩
theorem model_pair (a b : aspis_core.field.CM31) :
    XRk_Field.field.CM31.add a b = ok (pair a b) := by
  simp only [XRk_Field.field.CM31.add, model_word, bind_tc_ok]
  rfl

def field (a b : aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨pair a.c0 b.c0,pair a.c1 b.c1⟩
theorem model_field (a b : aspis_core.field.QM31) :
    aspis_core.field.QM31.add a b = ok (field a b) := by
  simp only [aspis_core.field.QM31.add, XRk_Field.field.QM31.add, model_pair, bind_tc_ok]
  rfl
#print axioms model_word
#print axioms model_pair
#print axioms model_field
end LPa.Add
