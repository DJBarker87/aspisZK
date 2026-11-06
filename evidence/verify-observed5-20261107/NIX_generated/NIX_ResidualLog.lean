import NIH_COMBINED_IMPORT
import RPv_JFy_CopyResidual
import NDO_JFy_CopyResidualValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ResidualLog
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (Canon)
abbrev Q := field.QM31
structure Inputs where
 v0 : Q
 v1 : Q
 v2 : Q
 v3 : Q
 v4 : Q
 v5 : Q
 v6 : Q
 v7 : Q
structure Replies where
 q0 : Q
 q1 : Q
 q2 : Q
 q3 : Q
 q4 : Q
 q5 : Q
 q6 : Q
 q7 : Q
 q8 : Q
 q9 : Q
 q10 : Q
 q11 : Q
 q12 : Q
 q13 : Q
 q14 : Q
 q15 : Q
 q16 : Q

def Reads (row : CopyRowExtension) (v : Inputs) : Prop :=
 row.producer_values.index_usize 0#usize=ok v.v0 ∧
 row.producer_values.index_usize 1#usize=ok v.v1 ∧
 row.producer_weights.index_usize 0#usize=ok v.v2 ∧
 row.producer_weights.index_usize 1#usize=ok v.v3 ∧
 row.consumer_values.index_usize 0#usize=ok v.v4 ∧
 row.consumer_values.index_usize 1#usize=ok v.v5 ∧
 row.consumer_weights.index_usize 0#usize=ok v.v6 ∧
 row.consumer_weights.index_usize 1#usize=ok v.v7

def Law (v : Inputs) (helper chi : Q) (r : Replies) : Prop :=
 field.QM31.sub chi v.v0=ok r.q0 ∧
 field.QM31.sub chi v.v1=ok r.q1 ∧
 field.QM31.sub chi v.v4=ok r.q2 ∧
 field.QM31.sub chi v.v5=ok r.q3 ∧
 field.QM31.mul r.q0 r.q1=ok r.q4 ∧
 field.QM31.mul r.q2 r.q3=ok r.q5 ∧
 field.QM31.mul v.v2 r.q1=ok r.q6 ∧
 field.QM31.mul v.v3 r.q0=ok r.q7 ∧
 field.QM31.add r.q6 r.q7=ok r.q8 ∧
 field.QM31.mul v.v6 r.q3=ok r.q9 ∧
 field.QM31.mul v.v7 r.q2=ok r.q10 ∧
 field.QM31.add r.q9 r.q10=ok r.q11 ∧
 field.QM31.mul helper r.q5=ok r.q12 ∧
 field.QM31.add r.q12 r.q11=ok r.q13 ∧
 field.QM31.mul r.q4 r.q13=ok r.q14 ∧
 field.QM31.mul r.q5 r.q8=ok r.q15 ∧
 field.QM31.sub r.q14 r.q15=ok r.q16

def Domain (v : Inputs) (helper chi : Q) (r : Replies) : Prop :=
 Canon helper ∧ Canon chi ∧ Canon v.v0 ∧ Canon v.v1 ∧ Canon v.v2 ∧ Canon v.v3 ∧ Canon v.v4 ∧ Canon v.v5 ∧ Canon v.v6 ∧ Canon v.v7 ∧ Canon r.q0 ∧ Canon r.q1 ∧ Canon r.q2 ∧ Canon r.q3 ∧ Canon r.q4 ∧ Canon r.q5 ∧ Canon r.q6 ∧ Canon r.q7 ∧ Canon r.q8 ∧ Canon r.q9 ∧ Canon r.q10 ∧ Canon r.q11 ∧ Canon r.q12 ∧ Canon r.q13 ∧ Canon r.q14 ∧ Canon r.q15 ∧ Canon r.q16

theorem array0 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 0#usize=ok a := by rfl
 theorem array1 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 1#usize=ok b := by rfl
 theorem array2 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 2#usize=ok c := by rfl
 theorem array3 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 3#usize=ok d := by rfl

theorem source_of_log (row : CopyRowExtension) (v : Inputs) (helper chi : Q) (r : Replies)
 (reads : Reads row v) (law : Law v helper chi r) :
 copy_residual row helper chi=ok r.q16 := by
 rcases reads with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 rcases law with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16⟩
 simp only [copy_residual,h0,h1,h2,h3,h4,h5,h6,h7,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,array0,array1,array2,array3,bind_tc_ok]

/-- Every input and opaque reply domain is derived for the same source row.
No copy_residual output or caller success is assumed. -/
theorem packet (row : CopyRowExtension) (helper chi : Q)
 (hpv : FIw_ArrayValue.canonical row.producer_values)
 (hpw : FIw_ArrayValue.canonical row.producer_weights)
 (hcv : FIw_ArrayValue.canonical row.consumer_values)
 (hcw : FIw_ArrayValue.canonical row.consumer_weights)
 (hh : Canon helper) (hc : Canon chi) :
 ∃ v r, Reads row v ∧ Law v helper chi r ∧ Domain v helper chi r ∧
 copy_residual row helper chi=ok r.q16 := by
 obtain ⟨v0,h0,d0⟩:=JFy_ArrayTotal.read row.producer_values 0#usize (by decide) hpv
 obtain ⟨v1,h1,d1⟩:=JFy_ArrayTotal.read row.producer_values 1#usize (by decide) hpv
 obtain ⟨v2,h2,d2⟩:=JFy_ArrayTotal.read row.producer_weights 0#usize (by decide) hpw
 obtain ⟨v3,h3,d3⟩:=JFy_ArrayTotal.read row.producer_weights 1#usize (by decide) hpw
 obtain ⟨v4,h4,d4⟩:=JFy_ArrayTotal.read row.consumer_values 0#usize (by decide) hcv
 obtain ⟨v5,h5,d5⟩:=JFy_ArrayTotal.read row.consumer_values 1#usize (by decide) hcv
 obtain ⟨v6,h6,d6⟩:=JFy_ArrayTotal.read row.consumer_weights 0#usize (by decide) hcw
 obtain ⟨v7,h7,d7⟩:=JFy_ArrayTotal.read row.consumer_weights 1#usize (by decide) hcw
 let v : Inputs:=⟨v0,v1,v2,v3,v4,v5,v6,v7⟩
 obtain ⟨q0,c0,e0,_⟩:=JFy_FieldTotal.sub chi v0 hc d0
 obtain ⟨q1,c1,e1,_⟩:=JFy_FieldTotal.sub chi v1 hc d1
 obtain ⟨q2,c2,e2,_⟩:=JFy_FieldTotal.sub chi v4 hc d4
 obtain ⟨q3,c3,e3,_⟩:=JFy_FieldTotal.sub chi v5 hc d5
 obtain ⟨q4,c4,e4,_⟩:=JFy_FieldTotal.mul q0 q1 e0 e1
 obtain ⟨q5,c5,e5,_⟩:=JFy_FieldTotal.mul q2 q3 e2 e3
 obtain ⟨q6,c6,e6,_⟩:=JFy_FieldTotal.mul v2 q1 d2 e1
 obtain ⟨q7,c7,e7,_⟩:=JFy_FieldTotal.mul v3 q0 d3 e0
 obtain ⟨q8,c8,e8,_⟩:=FIv_PreparedTotal.add q6 q7 e6 e7
 obtain ⟨q9,c9,e9,_⟩:=JFy_FieldTotal.mul v6 q3 d6 e3
 obtain ⟨q10,c10,e10,_⟩:=JFy_FieldTotal.mul v7 q2 d7 e2
 obtain ⟨q11,c11,e11,_⟩:=FIv_PreparedTotal.add q9 q10 e9 e10
 obtain ⟨q12,c12,e12,_⟩:=JFy_FieldTotal.mul helper q5 hh e5
 obtain ⟨q13,c13,e13,_⟩:=FIv_PreparedTotal.add q12 q11 e12 e11
 obtain ⟨q14,c14,e14,_⟩:=JFy_FieldTotal.mul q4 q13 e4 e13
 obtain ⟨q15,c15,e15,_⟩:=JFy_FieldTotal.mul q5 q8 e5 e8
 obtain ⟨q16,c16,e16,_⟩:=JFy_FieldTotal.sub q14 q15 e14 e15
 let r : Replies:=⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16⟩
 have reads : Reads row v:=⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 have law : Law v helper chi r:=⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16⟩
 exact ⟨v,r,reads,law,⟨hh,hc,d0,d1,d2,d3,d4,d5,d6,d7,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16⟩,source_of_log row v helper chi r reads law⟩

#print axioms array0
#print axioms array1
#print axioms array2
#print axioms array3
#print axioms source_of_log
#print axioms packet
end AspisR1.NIX_ResidualLog
end
