import NFG_InverseRef.Funs
set_option autoImplicit false
namespace NFG_InverseZeroDomain
open Aeneas Aeneas.Std Result NFG_InverseRef
def AllZero (x : field.QM31) : Prop := x.c0.a=0#u32 ∧ x.c0.b=0#u32 ∧ x.c1.a=0#u32 ∧ x.c1.b=0#u32
/-- Every raw prestate accepted by the zero guard is the zero fixture; no
canonical-only strengthening and no nonzero field arithmetic is used. -/
theorem test (x : field.QM31) : field.QM31.is_zero x=ok true ↔ AllZero x := by
 simp only [field.QM31.is_zero,field.CM31.is_zero,field.M31.is_zero,bind_tc_ok]
 split_ifs <;> simp_all [AllZero]
theorem unique (x : field.QM31) (zero : field.QM31.is_zero x=ok true) :
 x=⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := by
 obtain ⟨a,b,c,d⟩ := (test x).mp zero
 rcases x with ⟨⟨_,_⟩,⟨_,_⟩⟩
 simp_all
#print axioms test
#print axioms unique
end NFG_InverseZeroDomain
