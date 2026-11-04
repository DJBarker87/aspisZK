import NEV_PrefixFinalAudit
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace NEV_PrefixPacket
open Aeneas Aeneas.Std Result AspisR1

/-- Full emitted Result with the modeled external state and empty effects.
The returned owned vector carries the new allocation's values; this does not
assert that the complete physical allocator heap is unchanged. -/
theorem result_state_effects {S Event : Type} (state : S) (flat : Slice U32)
    (bound : flat.val.length≤110) :
    ∃ prefixes product,
      NEB_PureFrame.run (Event:=Event) state (NEG_PrefixFull.batch_prefix_products flat) =
        ok ((prefixes,product),state,[]) ∧
      (prefixes.val,product)=S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  obtain ⟨prefixes,product,run,meaning⟩ := NEI_PrefixStep.total flat bound
  exact ⟨prefixes,product,NEB_PureFrame.successful state _ _ run,meaning⟩

#print axioms result_state_effects
end NEV_PrefixPacket
end
