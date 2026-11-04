import NFE_NFC_FirstJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_FirstSource
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources
/-- The precise source window is retained, not replaced by an independent
successful decoder observation. -/
theorem cut (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (value : NE) (scalar : NQ) (run : first q g slot=ok (value,scalar)) :
    ∃ base start stop,
      Array.index_usize g 28#usize=ok value ∧
      slot*120#usize=ok base ∧ base+104#usize=ok start ∧ base+120#usize=ok stop ∧
      NFA_TailQM.read q start stop=ok scalar := by
  unfold first at run
  obtain ⟨w,read,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨base,mul,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start,startEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop,stopEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x,decode,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same : (w,x)=(value,scalar) := Result.ok.inj run
  cases same
  exact ⟨base,start,stop,read,mul,startEq,stopEq,decode⟩

theorem domains (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (canonical : NEV_DotInputs.Canonical g) (value : NE) (scalar : NQ)
    (run : first q g slot=ok (value,scalar)) : canonE value ∧ canonQ scalar := by
  obtain ⟨base,start,stop,read,_,_,_,decode⟩:=cut q g slot value scalar run
  exact ⟨NEV_DotInputs.selected g canonical _ (by decide) value read,
    NFA_TailQM.source q start stop scalar decode⟩
#print axioms cut
#print axioms domains
end AspisR1.NFE_NFC_FirstSource
end
