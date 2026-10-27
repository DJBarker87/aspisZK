import RPv_JFy_Specs
import RPv_FIw_CopyMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CopyResidual
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (r : CopyRowExtension) (helper chi : field.QM31)
    (hpv : canonical r.producer_values) (hcv : canonical r.consumer_values)
    (hpw : canonical r.producer_weights) (hcw : canonical r.consumer_weights)
    (hh : Canon helper) (hc : Canon chi) :
    ∃ out,copy_residual r helper chi=ok out ∧ Canon out := by
  obtain ⟨q,call_q,canon_q⟩ := JFy_ArrayTotal.read r.producer_values 0#usize (by decide) hpv
  obtain ⟨q1,call_q1,canon_q1,_⟩ := JFy_FieldTotal.sub chi q hc canon_q
  obtain ⟨q2,call_q2,canon_q2⟩ := JFy_ArrayTotal.read r.producer_values 1#usize (by decide) hpv
  obtain ⟨q3,call_q3,canon_q3,_⟩ := JFy_FieldTotal.sub chi q2 hc canon_q2
  obtain ⟨q4,call_q4,canon_q4⟩ := JFy_ArrayTotal.read r.consumer_values 0#usize (by decide) hcv
  obtain ⟨q5,call_q5,canon_q5,_⟩ := JFy_FieldTotal.sub chi q4 hc canon_q4
  obtain ⟨q6,call_q6,canon_q6⟩ := JFy_ArrayTotal.read r.consumer_values 1#usize (by decide) hcv
  obtain ⟨q7,call_q7,canon_q7,_⟩ := JFy_FieldTotal.sub chi q6 hc canon_q6
  obtain ⟨q8,call_q8,canon_q8⟩ := JFy_ArrayTotal.read (Array.make 4#usize [ q1, q3, q5, q7 ]) 0#usize (by decide) (by intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl|rfl <;> assumption)
  obtain ⟨q9,call_q9,canon_q9⟩ := JFy_ArrayTotal.read (Array.make 4#usize [ q1, q3, q5, q7 ]) 1#usize (by decide) (by intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl|rfl <;> assumption)
  obtain ⟨producer_denominator,call_producer_denominator,canon_producer_denominator,_⟩ := JFy_FieldTotal.mul q8 q9 canon_q8 canon_q9
  obtain ⟨q10,call_q10,canon_q10⟩ := JFy_ArrayTotal.read (Array.make 4#usize [ q1, q3, q5, q7 ]) 2#usize (by decide) (by intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl|rfl <;> assumption)
  obtain ⟨q11,call_q11,canon_q11⟩ := JFy_ArrayTotal.read (Array.make 4#usize [ q1, q3, q5, q7 ]) 3#usize (by decide) (by intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl|rfl <;> assumption)
  obtain ⟨consumer_denominator,call_consumer_denominator,canon_consumer_denominator,_⟩ := JFy_FieldTotal.mul q10 q11 canon_q10 canon_q11
  obtain ⟨q12,call_q12,canon_q12⟩ := JFy_ArrayTotal.read r.producer_weights 0#usize (by decide) hpw
  obtain ⟨q13,call_q13,canon_q13,_⟩ := JFy_FieldTotal.mul q12 q9 canon_q12 canon_q9
  obtain ⟨q14,call_q14,canon_q14⟩ := JFy_ArrayTotal.read r.producer_weights 1#usize (by decide) hpw
  obtain ⟨q15,call_q15,canon_q15,_⟩ := JFy_FieldTotal.mul q14 q8 canon_q14 canon_q8
  obtain ⟨producer_numerator,call_producer_numerator,canon_producer_numerator,_⟩ := FIv_PreparedTotal.add q13 q15 canon_q13 canon_q15
  obtain ⟨q16,call_q16,canon_q16⟩ := JFy_ArrayTotal.read r.consumer_weights 0#usize (by decide) hcw
  obtain ⟨q17,call_q17,canon_q17,_⟩ := JFy_FieldTotal.mul q16 q11 canon_q16 canon_q11
  obtain ⟨q18,call_q18,canon_q18⟩ := JFy_ArrayTotal.read r.consumer_weights 1#usize (by decide) hcw
  obtain ⟨q19,call_q19,canon_q19,_⟩ := JFy_FieldTotal.mul q18 q10 canon_q18 canon_q10
  obtain ⟨consumer_numerator,call_consumer_numerator,canon_consumer_numerator,_⟩ := FIv_PreparedTotal.add q17 q19 canon_q17 canon_q19
  obtain ⟨q20,call_q20,canon_q20,_⟩ := JFy_FieldTotal.mul helper consumer_denominator hh canon_consumer_denominator
  obtain ⟨q21,call_q21,canon_q21,_⟩ := FIv_PreparedTotal.add q20 consumer_numerator canon_q20 canon_consumer_numerator
  obtain ⟨q22,call_q22,canon_q22,_⟩ := JFy_FieldTotal.mul producer_denominator q21 canon_producer_denominator canon_q21
  obtain ⟨q23,call_q23,canon_q23,_⟩ := JFy_FieldTotal.mul consumer_denominator producer_numerator canon_consumer_denominator canon_producer_numerator
  obtain ⟨out,call_out,canon_out,_⟩ := JFy_FieldTotal.sub q22 q23 canon_q22 canon_q23
  refine ⟨out,?_,canon_out⟩
  unfold copy_residual
  rw [call_q,bind_tc_ok,call_q1,bind_tc_ok,call_q2,bind_tc_ok,call_q3,bind_tc_ok,call_q4,bind_tc_ok,call_q5,bind_tc_ok,call_q6,bind_tc_ok,call_q7,bind_tc_ok,call_q8,bind_tc_ok,call_q9,bind_tc_ok,call_producer_denominator,bind_tc_ok,call_q10,bind_tc_ok,call_q11,bind_tc_ok,call_consumer_denominator,bind_tc_ok,call_q12,bind_tc_ok,call_q13,bind_tc_ok,call_q14,bind_tc_ok,call_q15,bind_tc_ok,call_producer_numerator,bind_tc_ok,call_q16,bind_tc_ok,call_q17,bind_tc_ok,call_q18,bind_tc_ok,call_q19,bind_tc_ok,call_consumer_numerator,bind_tc_ok,call_q20,bind_tc_ok,call_q21,bind_tc_ok,call_q22,bind_tc_ok,call_q23,bind_tc_ok,call_out]
#print axioms source
end AspisR1.JFy_CopyResidual
end
