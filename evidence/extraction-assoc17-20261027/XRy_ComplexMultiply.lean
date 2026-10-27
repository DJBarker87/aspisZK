import XRy_Cross64
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersComplex XRy_Cross64
set_option autoImplicit false
namespace XRy_ComplexMultiply

theorem graph (a b : EC) :
 XRn_Join_Field.field.CM31.mul a b = (do
   let m0 ← XRn_Join_Field.field.M31.mul a.a b.a
   let m1 ← XRn_Join_Field.field.M31.mul a.b b.b
   let m2 ← XRn_Join_Field.field.M31.reduce_u64
     (U64.wrapping_mul (U64.wrapping_add (widen a.a) (widen a.b))
       (U64.wrapping_add (widen b.a) (widen b.b)))
   let low ← XRn_Join_Field.field.M31.sub m0 m1
   let high0 ← XRn_Join_Field.field.M31.sub m2 m0
   let high ← XRn_Join_Field.field.M31.sub high0 m1
   ok (⟨low,high⟩ : EC)) := by
 simp only [XRn_Join_Field.field.CM31.mul,lift,bind_tc_ok]

theorem multiply (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 mapR toC (XRn_Join_Field.field.CM31.mul a b) =
 AspisR1Qm31ArithmeticProbe.field.CM31.mul (toC a) (toC b) := by
 obtain ⟨m0,e0,c0,v0,h0⟩ := XRt_CohortMultiply.canonical_output a.a b.a
 obtain ⟨m1,e1,c1,v1,h1⟩ := XRt_CohortMultiply.canonical_output a.b b.b
 let product := U64.wrapping_mul (U64.wrapping_add (widen a.a) (widen a.b))
   (U64.wrapping_add (widen b.a) (widen b.b))
 obtain ⟨m2,c2,v2,h2⟩ := AspisR1.ExtractedCurrentReducer.current_wrapper_mod product
 have e2 := (XRy_Reducer64.reducer product).trans c2
 obtain ⟨low,cl,vl,hl⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod m0 m1 h0 h1
 obtain ⟨high0,ch0,vh0,hh0⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod m2 m0 h2 h0
 obtain ⟨high,ch,vh,hh⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod high0 m1 hh0 h1
 have el := (XRq_ScalarSub.sub m0 m1 h0 h1).trans cl
 have eh0 := (XRq_ScalarSub.sub m2 m0 h2 h0).trans ch0
 have eh := (XRq_ScalarSub.sub high0 m1 hh0 h1).trans ch
 dsimp only [product] at e2 c2
 rw [graph,AspisR1.ExtractedCurrentCM31Mul.generated_mul_graph,fragment a b ha hb]
 simp only [toC,e0,e1,e2,c0,c1,c2,el,eh0,eh,cl,ch0,ch,bind_tc_ok,mapR]

#print axioms graph
#print axioms multiply
end XRy_ComplexMultiply
