import AspisR1.CopyLinkLoopCandidate
import CopyLinkWeightExact

/-! Only literal integer descriptor bounds are checked here. No finite-field
arithmetic, recurrence, registry fold or generated certificate is normalized. -/
set_option autoImplicit false
namespace AspisR1.CopyRegistryBounds
open Aeneas Aeneas.Std
open AspisR1.CopyLinkWeightExact
abbrev registry := AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS

def DescriptorValid (link : Raw) : Prop :=
  link.tag.val < 2147483647 ∧ link.weight_kind.val < 5 ∧ link.weight_level.val < 64 ∧
  link.producer.row.val < 1024 ∧ link.producer.slot.val < 2 ∧ link.producer.pattern.val < 14 ∧
  link.consumer.row.val < 1024 ∧ link.consumer.slot.val < 2 ∧ link.consumer.pattern.val < 14

instance (link : Raw) : Decidable (DescriptorValid link) :=
  inferInstanceAs (Decidable (link.tag.val < 2147483647 ∧ link.weight_kind.val < 5 ∧ link.weight_level.val < 64 ∧
    link.producer.row.val < 1024 ∧ link.producer.slot.val < 2 ∧ link.producer.pattern.val < 14 ∧
    link.consumer.row.val < 1024 ∧ link.consumer.slot.val < 2 ∧ link.consumer.pattern.val < 14))

theorem registry_valid : List.Forall DescriptorValid registry.val := by
  unfold registry AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS
  decide

theorem member_bounds (link : Raw) (hmem : link ∈ registry.val) :
    link.tag.val < AspisR1.TerminalLiftM31Exact.P ∧ link.weight_kind.val < 5 ∧
    link.weight_level.val < 64 ∧ EndpointBounds link := by
  have h := (List.forall_iff_forall_mem.mp registry_valid) link hmem
  rcases h with ⟨htag,hkind,hlevel,hpr,hps,hpp,hcr,hcs,hcp⟩
  exact ⟨htag,hkind,hlevel,⟨hpr,hps,hpp,hcr,hcs,hcp⟩⟩

#print axioms registry_valid
#print axioms member_bounds
end AspisR1.CopyRegistryBounds
