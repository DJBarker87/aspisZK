import RPu_FIq_CopyPrefix
import RPu_FIv_SubMap
import RPu_FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CopyMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIv_NativeArray (value)
abbrev Row := pool_v1.pair_forest_copy_terminal.CopyRowExtension

def residual (row : Row) (helper chi : K) : K :=
  let p0 := chi-value row.producer_values 0
  let p1 := chi-value row.producer_values 1
  let c0 := chi-value row.consumer_values 0
  let c1 := chi-value row.consumer_values 1
  (p0*p1)*(helper*(c0*c1)+(value row.consumer_weights 0*c1+value row.consumer_weights 1*c0))-
    (c0*c1)*(value row.producer_weights 0*p1+value row.producer_weights 1*p0)

/-- Symbolic exact value of the installed copy residual, without reducing
its 136-link producer. Canonical link-accumulation outputs are explicit. -/
theorem value_exact (row : Row) (helper chi out : NQ)
    (hpv : ∀ x∈row.producer_values.val,Canon x)
    (hcv : ∀ x∈row.consumer_values.val,Canon x)
    (hpw : ∀ x∈row.producer_weights.val,Canon x)
    (hcw : ∀ x∈row.consumer_weights.val,Canon x)
    (hh : Canon helper) (hc : Canon chi)
    (run : pool_v1.pair_forest_copy_terminal.copy_residual row helper chi=ok out) :
    Canon out ∧ decode out=residual row (decode helper) (decode chi) := by
  unfold pool_v1.pair_forest_copy_terminal.copy_residual at run
  obtain ⟨q,h_q,r1⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q1,h_q1,r2⟩ := FIv_Map.bind_success _ _ _ r1
  obtain ⟨q2,h_q2,r3⟩ := FIv_Map.bind_success _ _ _ r2
  obtain ⟨q3,h_q3,r4⟩ := FIv_Map.bind_success _ _ _ r3
  obtain ⟨q4,h_q4,r5⟩ := FIv_Map.bind_success _ _ _ r4
  obtain ⟨q5,h_q5,r6⟩ := FIv_Map.bind_success _ _ _ r5
  obtain ⟨q6,h_q6,r7⟩ := FIv_Map.bind_success _ _ _ r6
  obtain ⟨q7,h_q7,r8⟩ := FIv_Map.bind_success _ _ _ r7
  obtain ⟨q8,h_q8,r9⟩ := FIv_Map.bind_success _ _ _ r8
  obtain ⟨q9,h_q9,r10⟩ := FIv_Map.bind_success _ _ _ r9
  obtain ⟨pd,h_pd,r11⟩ := FIv_Map.bind_success _ _ _ r10
  obtain ⟨q10,h_q10,r12⟩ := FIv_Map.bind_success _ _ _ r11
  obtain ⟨q11,h_q11,r13⟩ := FIv_Map.bind_success _ _ _ r12
  obtain ⟨cd,h_cd,r14⟩ := FIv_Map.bind_success _ _ _ r13
  obtain ⟨q12,h_q12,r15⟩ := FIv_Map.bind_success _ _ _ r14
  obtain ⟨q13,h_q13,r16⟩ := FIv_Map.bind_success _ _ _ r15
  obtain ⟨q14,h_q14,r17⟩ := FIv_Map.bind_success _ _ _ r16
  obtain ⟨q15,h_q15,r18⟩ := FIv_Map.bind_success _ _ _ r17
  obtain ⟨pn,h_pn,r19⟩ := FIv_Map.bind_success _ _ _ r18
  obtain ⟨q16,h_q16,r20⟩ := FIv_Map.bind_success _ _ _ r19
  obtain ⟨q17,h_q17,r21⟩ := FIv_Map.bind_success _ _ _ r20
  obtain ⟨q18,h_q18,r22⟩ := FIv_Map.bind_success _ _ _ r21
  obtain ⟨q19,h_q19,r23⟩ := FIv_Map.bind_success _ _ _ r22
  obtain ⟨cn,h_cn,r24⟩ := FIv_Map.bind_success _ _ _ r23
  obtain ⟨q20,h_q20,r25⟩ := FIv_Map.bind_success _ _ _ r24
  obtain ⟨q21,h_q21,r26⟩ := FIv_Map.bind_success _ _ _ r25
  obtain ⟨q22,h_q22,r27⟩ := FIv_Map.bind_success _ _ _ r26
  obtain ⟨q23,h_q23,r28⟩ := FIv_Map.bind_success _ _ _ r27
  have e_q8 : q8=q1 := by
    have slot := FIv_NativeArray.slot _ _ _ h_q8
    change some q1=some q8 at slot
    exact (Option.some.inj slot).symm
  subst q8
  have e_q9 : q9=q3 := by
    have slot := FIv_NativeArray.slot _ _ _ h_q9
    change some q3=some q9 at slot
    exact (Option.some.inj slot).symm
  subst q9
  have e_q10 : q10=q5 := by
    have slot := FIv_NativeArray.slot _ _ _ h_q10
    change some q5=some q10 at slot
    exact (Option.some.inj slot).symm
  subst q10
  have e_q11 : q11=q7 := by
    have slot := FIv_NativeArray.slot _ _ _ h_q11
    change some q7=some q11 at slot
    exact (Option.some.inj slot).symm
  subst q11
  have c_q := FIv_NativeArray.canonical row.producer_values _ q hpv h_q
  have v_q := FIv_NativeArray.read row.producer_values _ q h_q
  have c_q2 := FIv_NativeArray.canonical row.producer_values _ q2 hpv h_q2
  have v_q2 := FIv_NativeArray.read row.producer_values _ q2 h_q2
  have c_q4 := FIv_NativeArray.canonical row.consumer_values _ q4 hcv h_q4
  have v_q4 := FIv_NativeArray.read row.consumer_values _ q4 h_q4
  have c_q6 := FIv_NativeArray.canonical row.consumer_values _ q6 hcv h_q6
  have v_q6 := FIv_NativeArray.read row.consumer_values _ q6 h_q6
  have c_q12 := FIv_NativeArray.canonical row.producer_weights _ q12 hpw h_q12
  have v_q12 := FIv_NativeArray.read row.producer_weights _ q12 h_q12
  have c_q14 := FIv_NativeArray.canonical row.producer_weights _ q14 hpw h_q14
  have v_q14 := FIv_NativeArray.read row.producer_weights _ q14 h_q14
  have c_q16 := FIv_NativeArray.canonical row.consumer_weights _ q16 hcw h_q16
  have v_q16 := FIv_NativeArray.read row.consumer_weights _ q16 h_q16
  have c_q18 := FIv_NativeArray.canonical row.consumer_weights _ q18 hcw h_q18
  have v_q18 := FIv_NativeArray.read row.consumer_weights _ q18 h_q18
  have a_q1 := FIv_SubMap.qm chi q q1 hc c_q h_q1
  have a_q3 := FIv_SubMap.qm chi q2 q3 hc c_q2 h_q3
  have a_q5 := FIv_SubMap.qm chi q4 q5 hc c_q4 h_q5
  have a_q7 := FIv_SubMap.qm chi q6 q7 hc c_q6 h_q7
  have a_pd := FIv_NativeValue.mul q1 q3 pd a_q1.1 a_q3.1 h_pd
  have a_cd := FIv_NativeValue.mul q5 q7 cd a_q5.1 a_q7.1 h_cd
  have a_q13 := FIv_NativeValue.mul q12 q3 q13 c_q12 a_q3.1 h_q13
  have a_q15 := FIv_NativeValue.mul q14 q1 q15 c_q14 a_q1.1 h_q15
  have a_pn := FIv_NativeValue.add q13 q15 pn a_q13.1 a_q15.1 h_pn
  have a_q17 := FIv_NativeValue.mul q16 q7 q17 c_q16 a_q7.1 h_q17
  have a_q19 := FIv_NativeValue.mul q18 q5 q19 c_q18 a_q5.1 h_q19
  have a_cn := FIv_NativeValue.add q17 q19 cn a_q17.1 a_q19.1 h_cn
  have a_q20 := FIv_NativeValue.mul helper cd q20 hh a_cd.1 h_q20
  have a_q21 := FIv_NativeValue.add q20 cn q21 a_q20.1 a_cn.1 h_q21
  have a_q22 := FIv_NativeValue.mul pd q21 q22 a_pd.1 a_q21.1 h_q22
  have a_q23 := FIv_NativeValue.mul cd pn q23 a_cd.1 a_pn.1 h_q23
  have final := FIv_SubMap.qm q22 q23 out a_q22.1 a_q23.1 r28
  refine ⟨final.1,?_⟩
  rw [final.2,a_q23.2,a_q22.2,a_q21.2,a_q20.2,a_cn.2,a_q19.2,a_q17.2,a_pn.2,a_q15.2,a_q13.2,a_cd.2,a_pd.2,a_q7.2,a_q5.2,a_q3.2,a_q1.2]
  dsimp only [residual]
  change value row.producer_values 0=decode q at v_q
  change value row.producer_values 1=decode q2 at v_q2
  change value row.consumer_values 0=decode q4 at v_q4
  change value row.consumer_values 1=decode q6 at v_q6
  change value row.producer_weights 0=decode q12 at v_q12
  change value row.producer_weights 1=decode q14 at v_q14
  change value row.consumer_weights 0=decode q16 at v_q16
  change value row.consumer_weights 1=decode q18 at v_q18
  rw [v_q,v_q2,v_q4,v_q6,v_q12,v_q14,v_q16,v_q18]

#print axioms value_exact
end AspisR1.FIw_CopyMeaning
end
