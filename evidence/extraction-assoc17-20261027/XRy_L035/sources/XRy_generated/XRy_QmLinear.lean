import XRy_QmMultiply
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersQAdd
set_option autoImplicit false
namespace XRy_QmLinear

theorem add (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 ∃ z, XRn_Join_Field.field.QM31.add a b = ok z ∧ CanonicalQ z ∧
 AspisR1CurrentWideMul.field.QM31.add (toQ a) (toQ b) = ok (toQ z) := by
 obtain ⟨lo,el,hl,tl⟩ := XRy_ComplexCanonical.add a.c0 b.c0 ha.1 hb.1
 obtain ⟨hi,eh,hh,th⟩ := XRy_ComplexCanonical.add a.c1 b.c1 ha.2 hb.2
 refine ⟨⟨lo,hi⟩,?_,⟨hl,hh⟩,?_⟩
 · simp only [XRn_Join_Field.field.QM31.add,el,eh,bind_tc_ok]
 · change AspisR1Qm31ArithmeticProbe.field.QM31.add (toQ a) (toQ b) = _
   simp only [AspisR1Qm31ArithmeticProbe.field.QM31.add,toQ,tl,th,bind_tc_ok]

theorem sub (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 ∃ z, XRn_Join_Field.field.QM31.sub a b = ok z ∧ CanonicalQ z ∧
 AspisR1CurrentWideMul.field.QM31.sub (toQ a) (toQ b) = ok (toQ z) := by
 obtain ⟨lo,el,hl,tl⟩ := XRy_ComplexCanonical.sub a.c0 b.c0 ha.1 hb.1
 obtain ⟨hi,eh,hh,th⟩ := XRy_ComplexCanonical.sub a.c1 b.c1 ha.2 hb.2
 refine ⟨⟨lo,hi⟩,?_,⟨hl,hh⟩,?_⟩
 · simp only [XRn_Join_Field.field.QM31.sub,el,eh,bind_tc_ok]
 · simp only [AspisR1CurrentWideMul.field.QM31.sub,toQ,tl,th,bind_tc_ok]

theorem mul_u_total (a : EQ) (ha : CanonicalQ a) :
 ∃ z, XRn_Join_Field.field.wide_exact.mul_u a = ok z ∧ CanonicalQ z ∧
 AspisR1CurrentWideMul.field.wide_exact.mul_u (toQ a) = ok (toQ z) := by
 obtain ⟨r,er,hr,tr⟩ := XRy_MulByR.total a.c1 ha.2
 refine ⟨⟨r,a.c0⟩,?_,⟨hr,ha.1⟩,?_⟩
 · simp only [XRn_Join_Field.field.wide_exact.mul_u,er,bind_tc_ok]
 · unfold AspisR1CurrentWideMul.field.wide_exact.mul_u
   change (do let r ← AspisR1Qm31ArithmeticProbe.field.mul_by_r (XRp_PowersComplex.toC a.c1)
              ok (⟨r,XRp_PowersComplex.toC a.c0⟩ : TQ)) = _
   rw [tr,bind_tc_ok]
   rfl

theorem mul_u (a : EQ) (ha : CanonicalQ a) :
 mapR toQ (XRn_Join_Field.field.wide_exact.mul_u a) =
 AspisR1CurrentWideMul.field.wide_exact.mul_u (toQ a) := by
 obtain ⟨z,hz,hc,ht⟩ := mul_u_total a ha
 rw [hz]
 exact ht.symm

#print axioms add
#print axioms sub
#print axioms mul_u_total
#print axioms mul_u
end XRy_QmLinear
