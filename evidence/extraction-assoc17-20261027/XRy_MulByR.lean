import XRy_ComplexCanonical
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersComplex
set_option autoImplicit false
namespace XRy_MulByR

theorem total (a : EC) (ha : Canonical a) :
 ∃ z, XRn_Join_Field.field.mul_by_r a = ok z ∧ Canonical z ∧
 AspisR1Qm31ArithmeticProbe.field.mul_by_r (toC a) = ok (toC z) := by
 obtain ⟨a2,ea2,va2,ca2⟩ :=
   AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.a a.a ha.1 ha.1
 obtain ⟨lo,elo,vlo,clo⟩ :=
   AspisR1.ExtractedCurrentM31AddSub.current_sub_mod a2 a.b ca2 ha.2
 obtain ⟨b2,eb2,vb2,cb2⟩ :=
   AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.b a.b ha.2 ha.2
 obtain ⟨hi,ehi,vhi,chi⟩ :=
   AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.a b2 ha.1 cb2
 have ra2 := (XRp_PowersScalar.add a.a a.a ha.1 ha.1).trans ea2
 have rlo := (XRq_ScalarSub.sub a2 a.b ca2 ha.2).trans elo
 have rb2 := (XRp_PowersScalar.add a.b a.b ha.2 ha.2).trans eb2
 have rhi := (XRp_PowersScalar.add a.a b2 ha.1 cb2).trans ehi
 refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
 · simp only [XRn_Join_Field.field.mul_by_r,XRn_Join_Field.field.M31.double,
     ra2,rlo,rb2,rhi,bind_tc_ok]
 · simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
     AspisR1Qm31ArithmeticProbe.field.M31.double,toC,ea2,elo,eb2,ehi,bind_tc_ok]

theorem same (a : EC) (ha : Canonical a) :
 mapR toC (XRn_Join_Field.field.mul_by_r a) =
 AspisR1Qm31ArithmeticProbe.field.mul_by_r (toC a) := by
 obtain ⟨z,hz,hc,ht⟩ := total a ha
 rw [hz,ht]
 rfl

#print axioms total
#print axioms same
end XRy_MulByR
