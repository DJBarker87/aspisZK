import JFv_OracleTotal
set_option autoImplicit false
namespace AspisR1.JFv_Begin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem pair {A B C : Type} (a : A) (b : B) (k : A → B → C) :
    (let (x,y) := (a,b); k x y)=k a b := rfl

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (pre : r1_wire.Prefix) (t0 : r1_wire.SemanticTranscript H) (initial : t0.next_row.val=0) :
    ∃ challenges after,r1_wire.begin D pre t0=ok (.Ok challenges,after) ∧ after.next_row.val=15 := by
  obtain ⟨r0,q0,t1,read0,row0,call0,next1,canon0⟩ := JFv_PrefixCall.success D total pre t0 0#u8
    (by apply UScalar.eq_of_val_eq;change 0=t0.next_row.val;omega) (by decide)
  change t1.next_row.val=1 at next1
  obtain ⟨r1,q1,t2,read1,row1,call1,next2,canon1⟩ := JFv_PrefixCall.success D total pre t1 1#u8
    (by apply UScalar.eq_of_val_eq;change 1=t1.next_row.val;omega) (by decide)
  change t2.next_row.val=2 at next2
  obtain ⟨r2,q2,t3,read2,row2,call2,next3,canon2⟩ := JFv_PrefixCall.success D total pre t2 2#u8
    (by apply UScalar.eq_of_val_eq;change 2=t2.next_row.val;omega) (by decide)
  change t3.next_row.val=3 at next3
  obtain ⟨r3,q3,t4,read3,row3,call3,next4,canon3⟩ := JFv_PrefixCall.success D total pre t3 3#u8
    (by apply UScalar.eq_of_val_eq;change 3=t3.next_row.val;omega) (by decide)
  change t4.next_row.val=4 at next4
  obtain ⟨r4,q4,t5,read4,row4,call4,next5,canon4⟩ := JFv_PrefixCall.success D total pre t4 4#u8
    (by apply UScalar.eq_of_val_eq;change 4=t4.next_row.val;omega) (by decide)
  change t5.next_row.val=5 at next5
  obtain ⟨r5,q5,t6,read5,row5,call5,next6,canon5⟩ := JFv_PrefixCall.success D total pre t5 5#u8
    (by apply UScalar.eq_of_val_eq;change 5=t5.next_row.val;omega) (by decide)
  change t6.next_row.val=6 at next6
  obtain ⟨r6,q6,t7,read6,row6,call6,next7,canon6⟩ := JFv_PrefixCall.success D total pre t6 6#u8
    (by apply UScalar.eq_of_val_eq;change 6=t6.next_row.val;omega) (by decide)
  change t7.next_row.val=7 at next7
  obtain ⟨r7,q7,t8,read7,row7,call7,next8,canon7⟩ := JFv_PrefixCall.success D total pre t7 7#u8
    (by apply UScalar.eq_of_val_eq;change 7=t7.next_row.val;omega) (by decide)
  change t8.next_row.val=8 at next8
  obtain ⟨r8,q8,t9,read8,row8,call8,next9,canon8⟩ := JFv_PrefixCall.success D total pre t8 8#u8
    (by apply UScalar.eq_of_val_eq;change 8=t8.next_row.val;omega) (by decide)
  change t9.next_row.val=9 at next9
  obtain ⟨r9,q9,t10,read9,row9,call9,next10,canon9⟩ := JFv_PrefixCall.success D total pre t9 9#u8
    (by apply UScalar.eq_of_val_eq;change 9=t9.next_row.val;omega) (by decide)
  change t10.next_row.val=10 at next10
  obtain ⟨r10,q10,t11,read10,row10,call10,next11,canon10⟩ := JFv_PrefixCall.success D total pre t10 10#u8
    (by apply UScalar.eq_of_val_eq;change 10=t10.next_row.val;omega) (by decide)
  change t11.next_row.val=11 at next11
  obtain ⟨r11,q11,t12,read11,row11,call11,next12,canon11⟩ := JFv_PrefixCall.success D total pre t11 11#u8
    (by apply UScalar.eq_of_val_eq;change 11=t11.next_row.val;omega) (by decide)
  change t12.next_row.val=12 at next12
  obtain ⟨r12,q12,t13,read12,row12,call12,next13,canon12⟩ := JFv_PrefixCall.success D total pre t12 12#u8
    (by apply UScalar.eq_of_val_eq;change 12=t12.next_row.val;omega) (by decide)
  change t13.next_row.val=13 at next13
  obtain ⟨r13,q13,t14,read13,row13,call13,next14,canon13⟩ := JFv_PrefixCall.success D total pre t13 13#u8
    (by apply UScalar.eq_of_val_eq;change 13=t13.next_row.val;omega) (by decide)
  change t14.next_row.val=14 at next14
  obtain ⟨r14,q14,t15,read14,row14,call14,next15,canon14⟩ := JFv_PrefixCall.success D total pre t14 14#u8
    (by apply UScalar.eq_of_val_eq;change 14=t14.next_row.val;omega) (by decide)
  change t15.next_row.val=15 at next15
  unfold r1_wire.begin
  simp (config := {zeta := true}) only [read0,call0,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read1,call1,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read2,call2,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read3,call3,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read4,call4,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read5,call5,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read6,call6,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read7,call7,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read8,call8,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read9,call9,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read10,call10,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read11,call11,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read12,call12,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read13,call13,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  simp (config := {zeta := true}) only [read14,call14,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,pair]
  exact ⟨_,t15,rfl,by change t15.next_row.val=15;omega⟩

#print axioms pair
#print axioms success
end AspisR1.JFv_Begin
