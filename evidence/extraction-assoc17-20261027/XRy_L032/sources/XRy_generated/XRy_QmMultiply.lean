import XRy_MulByR
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersQAdd
set_option autoImplicit false
namespace XRy_QmMultiply

theorem total (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 ∃ z, XRn_Join_Field.field.QM31.mul a b = ok z ∧ CanonicalQ z ∧
 AspisR1Qm31ArithmeticProbe.field.QM31.mul (toQ a) (toQ b) = ok (toQ z) := by
 obtain ⟨m0,e0,h0,t0⟩ := XRy_ComplexCanonical.mul a.c0 b.c0 ha.1 hb.1
 obtain ⟨m1,e1,h1,t1⟩ := XRy_ComplexCanonical.mul a.c1 b.c1 ha.2 hb.2
 obtain ⟨aa,ea,ha',ta⟩ := XRy_ComplexCanonical.add a.c0 a.c1 ha.1 ha.2
 obtain ⟨bb,eb,hb',tb⟩ := XRy_ComplexCanonical.add b.c0 b.c1 hb.1 hb.2
 obtain ⟨m2,e2,h2,t2⟩ := XRy_ComplexCanonical.mul aa bb ha' hb'
 obtain ⟨r,er,hr,tr⟩ := XRy_MulByR.total m1 h1
 obtain ⟨lo,el,hl,tl⟩ := XRy_ComplexCanonical.add m0 r h0 hr
 obtain ⟨d,ed,hd,td⟩ := XRy_ComplexCanonical.sub m2 m0 h2 h0
 obtain ⟨hi,eh,hh,th⟩ := XRy_ComplexCanonical.sub d m1 hd h1
 refine ⟨⟨lo,hi⟩,?_,⟨hl,hh⟩,?_⟩
 · simp only [XRn_Join_Field.field.QM31.mul,e0,e1,ea,eb,e2,er,el,ed,eh,bind_tc_ok]
 · simp only [AspisR1Qm31ArithmeticProbe.field.QM31.mul,toQ,t0,t1,ta,tb,t2,tr,tl,td,th,bind_tc_ok]

theorem multiply (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 mapR toQ (XRn_Join_Field.field.QM31.mul a b) =
 AspisR1CurrentWideMul.field.QM31.mul (toQ a) (toQ b) := by
 obtain ⟨z,hz,hc,ht⟩ := total a b ha hb
 rw [hz,ht]
 rfl

#print axioms total
#print axioms multiply
end XRy_QmMultiply
