import FJi_TailInputs
import FJi_DecodeUnwrap
import FJf_EbyKNew
import FIo_ArrayCanon
import FIp_ArrayValue
import JFs_TX2_DotSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_TailTrace
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FJi_Accumulations FJi_TailInputs
open FIo_FieldBridge (NQ wide)
def model (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) : AspisWideTower.WideExact :=
  FIp_ArrayValue.value g 28*FJf_EbyKCodec.scalar (observed (read0 q slot))+
    FIp_ArrayValue.value g 26*FJf_EbyKCodec.scalar (observed (read1 q slot))+
    FIp_ArrayValue.value g 27*FJf_EbyKCodec.scalar (observed (read2 q slot))

/-- The three SAME tail fields and coefficients of the installed source call.
Canonical powers remain explicit here and will be supplied by their constructor. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (hg : FIo_ArrayCanon.Holds g) (run : JFs_TX2_DotSuffix.tail q g slot=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=model q g slot := by
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
  have c26 : i14=26#usize := Result.ok.inj (Hi14.symm.trans (show (0#usize+26#usize : Result Usize)=ok 26#usize from by scalar_tac))
  have c27 : i18=27#usize := Result.ok.inj (Hi18.symm.trans (show (1#usize+26#usize : Result Usize)=ok 27#usize from by scalar_tac))
  subst i14; subst i18
  have hread0 : read0 q slot=ok q1 := by
    simp only [read0,Hi8,Hi9,Hi10,Hs,Ho1,Hq1,bind_tc_ok]
  have hread1 : read1 q slot=ok q2 := by
    simp only [read1,Hi11,Hi12,Hi13,Hoffset0,Hi15,Hs1,Ho2,Hq2,bind_tc_ok]
  have hread2 : read2 q slot=ok q3 := by
    simp only [read2,Hi11,Hi16,Hi17,Hoffset1,Hi19,Hs2,Ho3,Hq3,bind_tc_ok]
  obtain ⟨count0,b0,m0⟩ := FJf_EbyKNew.value tail Htail
  have p0 := FJf_EbyKPush.value tail tail1 we q1 (FIo_ArrayCanon.read g _ _ hg Hwe)
    (FJi_DecodeUnwrap.value s o1 q1 Ho1 Hq1) b0 Htail1
  have p1 := FJf_EbyKPush.value tail1 tail2 we1 q2 (FIo_ArrayCanon.read g _ _ hg Hwe1)
    (FJi_DecodeUnwrap.value s1 o2 q2 Ho2 Hq2) p0.2.1 Htail2
  have p2 := FJf_EbyKPush.value tail2 tail3 we2 q3 (FIo_ArrayCanon.read g _ _ hg Hwe2)
    (FJi_DecodeUnwrap.value s2 o3 q3 Ho3 Hq3) p1.2.1 Htail3
  have finish := FJf_EbyKFinish.value tail3 we3 Hwe3
  refine ⟨finish.1,?_⟩
  rw [finish.2,p2.2.2,p1.2.2,p0.2.2,m0,zero_add]
  unfold model
  rw [observed_value _ q1 hread0,observed_value _ q2 hread1,observed_value _ q3 hread2,
    FIp_ArrayValue.read g 28#usize we Hwe,FIp_ArrayValue.read g 26#usize we1 Hwe1,
    FIp_ArrayValue.read g 27#usize we2 Hwe2]
#print axioms value
end AspisR1.FJi_TailTrace
end
