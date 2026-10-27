import XRy_ComplexMultiply
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersComplex
set_option autoImplicit false
namespace XRy_ComplexCanonical

theorem of_map_ok {A B : Type} (f : A → B) (r : Result A) (b : B)
 (h : mapR f r = ok b) : ∃ a, r=ok a ∧ f a=b := by
 cases r with
 | ok a => exact ⟨a,rfl,Result.ok.inj h⟩
 | fail e => cases h
 | div => cases h

theorem mul (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 ∃ z, XRn_Join_Field.field.CM31.mul a b = ok z ∧ Canonical z ∧
 AspisR1Qm31ArithmeticProbe.field.CM31.mul (toC a) (toC b) = ok (toC z) := by
 obtain ⟨w,hw,hc,_,_⟩ := AspisR1.ExtractedCurrentCM31Mul.current_mul_words
   (toC a) (toC b) ha hb
 obtain ⟨z,hz,he⟩ := of_map_ok toC _ w ((XRy_ComplexMultiply.multiply a b ha hb).trans hw)
 refine ⟨z,hz,?_,?_⟩
 · rw [←he] at hc
   exact hc
 · exact hw.trans (congrArg ok he.symm)

theorem add (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 ∃ z, XRn_Join_Field.field.CM31.add a b = ok z ∧ Canonical z ∧
 AspisR1Qm31ArithmeticProbe.field.CM31.add (toC a) (toC b) = ok (toC z) := by
 obtain ⟨w,hw,hc,_,_⟩ := AspisR1.ExtractedCurrentTowerAdd.current_cm_add_mod
   (toC a) (toC b) ha hb
 obtain ⟨z,hz,he⟩ := of_map_ok toC _ w ((XRp_PowersComplex.add a b ha hb).trans hw)
 refine ⟨z,hz,?_,?_⟩
 · rw [←he] at hc
   exact hc
 · exact hw.trans (congrArg ok he.symm)

theorem sub (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 ∃ z, XRn_Join_Field.field.CM31.sub a b = ok z ∧ Canonical z ∧
 AspisR1Qm31ArithmeticProbe.field.CM31.sub (toC a) (toC b) = ok (toC z) := by
 obtain ⟨w,hw,hc,_,_⟩ := AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod
   (toC a) (toC b) ha hb
 obtain ⟨z,hz,he⟩ := of_map_ok toC _ w ((XRq_ComplexSub.sub a b ha hb).trans hw)
 refine ⟨z,hz,?_,?_⟩
 · rw [←he] at hc
   exact hc
 · exact hw.trans (congrArg ok he.symm)

#print axioms of_map_ok
#print axioms mul
#print axioms add
#print axioms sub
end XRy_ComplexCanonical
