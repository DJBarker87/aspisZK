import NFC_HeadDomain
import NFC_TailState
import NFC_AddDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_DotDomain
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- Complete accepted actual dot has canonical head, tail and result. Every
cut is derived from the same run; no assumed successful child observation. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (out : NE) (canonical : NEV_DotInputs.Canonical g)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    canonE out ∧ ∃ limbs head tail,
      FIp_NativeDots.fast_dots.four_dots_one_loop0 (NFA_Iterator.value 0) q g slot
        (Array.repeat 8#usize 0#u64)=ok limbs ∧
      NFA_FoldEight.Bound limbs 7 ∧
      NFA_SuffixFactor.scalarFinish limbs=ok head ∧ canonE head ∧
      NFA_SuffixFactor.tail q g slot=ok tail ∧ canonE tail ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail=ok out := by
  obtain ⟨limbs,head,tail,loop,bound,finish,tailRun,add⟩:=NFA_DotCuts.accepted q g slot out run
  have ch:=NFC_HeadDomain.canonical limbs head finish
  have ct:=(NFC_TailState.accepted q g slot tail canonical tailRun).1
  exact ⟨NFC_AddDomain.canonical head tail out ch ct add,
    limbs,head,tail,loop,bound,finish,ch,tailRun,ct,add⟩
#print axioms accepted
end AspisR1.NFC_DotDomain
end
