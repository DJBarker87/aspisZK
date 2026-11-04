import NFA_DotCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_TailTrace
open Aeneas Aeneas.Std Result NEV_DotCarrier
abbrev Acc := FIo_Native.fast_pairing.EbyKDot

theorem unwrap_unit (r : core.result.Result Unit Unit)
    (run : core.result.Result.unwrap core.fmt.DebugUnit r=ok ()) : r=.Ok () := by
  cases r with
  | Ok v => cases v; rfl
  | Err e => cases run

/-- Three ordered actual receiver transitions from one accepted tail. The
coefficient reads, decoded scalar domains and finish belong to those same calls. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (out : NE) (canonical : NEV_DotInputs.Canonical g)
    (run : NFA_SuffixFactor.tail q g slot=ok out) :
    ∃ (s0 s1 s2 s3 : Acc) (w0 w1 w2 : NE) (x0 x1 x2 : NQ),
      FIo_Native.fast_pairing.EbyKDot.new=ok s0 ∧
      Array.index_usize g 28#usize=ok w0 ∧
      Array.index_usize g 26#usize=ok w1 ∧
      Array.index_usize g 27#usize=ok w2 ∧
      canonE w0 ∧ canonE w1 ∧ canonE w2 ∧
      canonQ x0 ∧ canonQ x1 ∧ canonQ x2 ∧
      FIo_Native.fast_pairing.EbyKDot.push s0 w0 x0=ok (.Ok (),s1) ∧
      FIo_Native.fast_pairing.EbyKDot.push s1 w1 x1=ok (.Ok (),s2) ∧
      FIo_Native.fast_pairing.EbyKDot.push s2 w2 x2=ok (.Ok (),s3) ∧
      FIo_Native.fast_pairing.EbyKDot.finish s3=ok out := by
  unfold NFA_SuffixFactor.tail at run
  obtain ⟨s0,new,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨w0,gw0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i8,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i9,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i10,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b0,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o0,decode0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x0,unwrap0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r0,s1⟩,push0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Aeneas.Std.uncurry] at run
  obtain ⟨u0,check0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases u0
  rw [unwrap_unit r0 check0] at push0
  obtain ⟨i11,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i12,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i13,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨off0,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Usize.add, Usize.mul, lift, bind_tc_ok] at run
  obtain ⟨w1,gw1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop1,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b1,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o1,decode1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x1,unwrap1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r1,s2⟩,push1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Aeneas.Std.uncurry] at run
  obtain ⟨u1,check1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases u1
  rw [unwrap_unit r1 check1] at push1
  obtain ⟨i16,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i17,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨off1,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Usize.add, Usize.mul, lift, bind_tc_ok] at run
  obtain ⟨w2,gw2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop2,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b2,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o2,decode2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x2,unwrap2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r2,s3⟩,push2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Aeneas.Std.uncurry] at run
  obtain ⟨u2,check2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases u2
  rw [unwrap_unit r2 check2] at push2
  simp only [bind_tc_ok] at run
  have scalar {b : Slice U8} {o : Option NQ} {x : NQ}
      (decode : FIp_DotDecode.field.QM31.from_le_bytes b=ok o)
      (unwrap : core.option.Option.unwrap o=ok x) : canonQ x := by
    cases o with
    | none => cases unwrap
    | some v =>
      have eq : v=x := Result.ok.inj unwrap
      subst v
      exact NFA_TailQM.qm b x decode
  refine ⟨s0,s1,s2,s3,w0,w1,w2,x0,x1,x2,new,gw0,gw1,gw2,?_,?_,?_,
    scalar decode0 unwrap0,scalar decode1 unwrap1,scalar decode2 unwrap2,push0,push1,push2,?_⟩
  · exact NEV_DotInputs.selected g canonical _ (by decide) w0 gw0
  · exact NEV_DotInputs.selected g canonical _ (by decide) w1 gw1
  · exact NEV_DotInputs.selected g canonical _ (by decide) w2 gw2
  · exact run
#print axioms unwrap_unit
#print axioms accepted
end AspisR1.NFC_TailTrace
end
