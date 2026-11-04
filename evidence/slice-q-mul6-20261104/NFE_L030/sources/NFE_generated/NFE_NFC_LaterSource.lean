import NFE_NFC_LaterJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_LaterSource
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources

theorem cut (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (base position : Usize) (value : NE) (scalar : NQ)
    (run : later q g base position=ok (value,scalar)) :
    ∃ origin offset start index stop,
      480#usize+base=ok origin ∧ position*16#usize=ok offset ∧ origin+offset=ok start ∧
      position+26#usize=ok index ∧ Array.index_usize g index=ok value ∧
      start+16#usize=ok stop ∧ NFA_TailQM.read q start stop=ok scalar := by
  unfold later at run
  obtain ⟨origin,originEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨offset,offsetEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start,startEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨index,indexEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨w,read,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop,stopEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x,decode,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same : (w,x)=(value,scalar) := Result.ok.inj run
  cases same
  exact ⟨origin,offset,start,index,stop,originEq,offsetEq,startEq,indexEq,read,stopEq,decode⟩

theorem domains (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (base position : Usize) (active : position.val<2)
    (canonical : NEV_DotInputs.Canonical g) (value : NE) (scalar : NQ)
    (run : later q g base position=ok (value,scalar)) : canonE value ∧ canonQ scalar := by
  obtain ⟨origin,offset,start,index,stop,_,_,_,indexEq,read,_,decode⟩:=cut q g base position value scalar run
  obtain ⟨actual,call,val⟩:=WP.spec_imp_exists
    (UScalar.add_spec (x:=position) (y:=26#usize) (by scalar_tac))
  have same : actual=index := Result.ok.inj (call.symm.trans indexEq)
  subst actual
  have bound : index.val<29 := by scalar_tac
  exact ⟨NEV_DotInputs.selected g canonical index bound value read,
    NFA_TailQM.source q start stop scalar decode⟩
#print axioms cut
#print axioms domains
end AspisR1.NFE_NFC_LaterSource
end
