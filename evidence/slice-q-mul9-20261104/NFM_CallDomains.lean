import NFM_Single
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFM_CallDomains
open Aeneas Aeneas.Std Result NEV_DotCarrier

/-- Every public tail call's actual count is within the frozen4096 limit.
The domain is derived for the SAME packet, not three independent receivers. -/
theorem tail_counts {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients}
    {slot : Usize} {out : NE} (packet : NFE_NFC_MainPacket.Packet q g slot out)
    (domain : NFE_WrapperBridge.NativeDomains packet) :
    packet.tailPacket.state0.count.val<4096 ∧
    packet.tailPacket.state1.count.val<4096 ∧
    packet.tailPacket.state2.count.val<4096 := by
  have a:=domain.2.1.1
  have b:=domain.2.1.2.1
  have c:=domain.2.1.2.2
  omega

/-- Reuse the existing exact emitted body for typed terminal selection.
Its codomain and terminal callee are WideExact; no new body is substituted.
Native selection is checked separately against the frozen typed Rust call. -/
theorem terminal (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) :
    FIp_NativeDots.fast_dots.four_dots_one q g slot = (do
      let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize,«end»:=26#usize} 4#usize
      let limbs ← FIp_NativeDots.fast_dots.four_dots_one_loop0 iter q g slot
        (Array.repeat 8#usize 0#u64)
      let head ← NFE_NFA_SuffixFactor.scalarFinish limbs
      let tail ← NFE_NFA_SuffixFactor.tail q g slot
      FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail) :=
  NFE_NFA_SuffixFactor.body q g slot

#print axioms tail_counts
#print axioms terminal
end AspisR1.NFM_CallDomains
end
