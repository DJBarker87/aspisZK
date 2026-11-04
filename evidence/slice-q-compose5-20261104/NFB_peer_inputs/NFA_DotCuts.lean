import NFA_SuffixFactor
import NFA_TailCounter
import NFA_BatchDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFA_DotCuts
open Aeneas Aeneas.Std Result
/-- All intermediate observations are DERIVED from the SAME actual successful
single-slot computation. This is a source-cut theorem, not a CLOSED dot row. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (value : NEV_DotCarrier.NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok value) :
    ∃ limbs head tail,
      FIp_NativeDots.fast_dots.four_dots_one_loop0 (NFA_Iterator.value 0) q g slot
        (Array.repeat 8#usize 0#u64)=ok limbs ∧
      NFA_FoldEight.Bound limbs 7 ∧
      NFA_SuffixFactor.scalarFinish limbs=ok head ∧
      NFA_SuffixFactor.tail q g slot=ok tail ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail=ok value := by
  rw [NFA_SuffixFactor.body] at run
  simp only [NFA_Iterator.initial,bind_tc_ok] at run
  obtain ⟨limbs,loop,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨head,finish,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tail,tailRun,add⟩:=Port3_PushFrame.bind_success _ _ _ run
  exact ⟨limbs,head,tail,loop,NFA_OuterLoop.initialized q g slot limbs loop,finish,tailRun,add⟩
#print axioms accepted
end AspisR1.NFA_DotCuts
end
