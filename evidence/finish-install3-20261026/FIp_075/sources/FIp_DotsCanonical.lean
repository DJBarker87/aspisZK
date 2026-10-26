import FIp_NativeDots
import FIp_FastFinishCanonical
import FIp_FromLimbsUnwrap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem helper (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) : FIo_WideValues.Canon out := by
  unfold FIp_NativeDots.fast_dots.four_dots_one at run
  obtain ⟨iter,Hiter,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨limbs1,Hlimbs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i,Hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m,Hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i1,Hi1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m1,Hm1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i2,Hi2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m2,Hm2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i3,Hi3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m3,Hm3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i4,Hi4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m4,Hm4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i5,Hi5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m5,Hm5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i6,Hi6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m6,Hm6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i7,Hi7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m7,Hm7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,Ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨value,Hvalue,run⟩ := Port3_PushFrame.bind_success _ _ _ run
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
  have headCanon := FIp_FromLimbsUnwrap.canonical _ o value Ho Hvalue
  have tailCanon := FIp_FastFinishCanonical.finish tail3 we3 Hwe3
  exact (FIo_WideValues.add value we3 out headCanon tailCanon run).1

#print axioms helper
end AspisR1.FIp_DotsCanonical
end
