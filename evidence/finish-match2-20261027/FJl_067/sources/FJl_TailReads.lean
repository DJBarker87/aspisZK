import FJi_TailTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_TailReads
open Aeneas Aeneas.Std Result
open FJi_Accumulations FJi_TailInputs
open FIo_FieldBridge (NQ)
/-- Read provenance only: preserve all three actual tail decoder calls.
The arithmetic VALUE is imported from FJi_TailTrace, not reproved. -/
theorem reached (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (run : JFs_TX2_DotSuffix.tail q g slot=ok out) :
    ∃ q0 q1 q2 : NQ,read0 q slot=ok q0 ∧ read1 q slot=ok q1 ∧ read2 q slot=ok q2 := by
  unfold JFs_TX2_DotSuffix.tail at run
  obtain ⟨tail,Htail,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we,Hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i8,Hi8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i9,Hi9,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i10,Hi10,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s,Hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o1,Ho1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,Hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r, tail1⟩,Htail1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨accepted0,Haccepted0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i11,Hi11,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i12,Hi12,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i13,Hi13,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨offset0,Hoffset0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i14,Hi14,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we1,Hwe1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i15,Hi15,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s1,Hs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o2,Ho2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,Hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r1, tail2⟩,Htail2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨accepted1,Haccepted1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i16,Hi16,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i17,Hi17,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨offset1,Hoffset1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i18,Hi18,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we2,Hwe2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i19,Hi19,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s2,Hs2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o3,Ho3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,Hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r2, tail3⟩,Htail3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨accepted2,Haccepted2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we3,Hwe3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : we3=out := Result.ok.inj run
  subst out
  have r0 : r=.Ok () := by cases r <;> first | rfl | cases Haccepted0
  have r1 : r1=.Ok () := by cases r1 <;> first | rfl | cases Haccepted1
  have r2 : r2=.Ok () := by cases r2 <;> first | rfl | cases Haccepted2
  subst r; subst r1; subst r2
  have c26 : i14=26#usize := by
    apply UScalar.eq_of_val_eq
    have h := FIw_WordValue.add 0#usize 26#usize i14 Hi14
    scalar_tac
  have c27 : i18=27#usize := by
    apply UScalar.eq_of_val_eq
    have h := FIw_WordValue.add 1#usize 26#usize i18 Hi18
    scalar_tac
  subst i14; subst i18
  have hread0 : read0 q slot=ok q1 := by
    simp only [read0,Hi8,Hi9,Hi10,Hs,Ho1,Hq1,bind_tc_ok]
  have hread1 : read1 q slot=ok q2 := by
    simp only [read1,Hi11,Hi12,Hi13,Hoffset0,Hi15,Hs1,Ho2,Hq2,bind_tc_ok]
  have hread2 : read2 q slot=ok q3 := by
    simp only [read2,Hi11,Hi16,Hi17,Hoffset1,Hi19,Hs2,Ho3,Hq3,bind_tc_ok]
  exact ⟨q1,q2,q3,hread0,hread1,hread2⟩
#print axioms reached
end AspisR1.FJl_TailReads
end
