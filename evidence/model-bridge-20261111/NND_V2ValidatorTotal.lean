import NND_ResultTotal
import NHY_NaturalReads
import NIS_EntryModel
set_option autoImplicit false
noncomputable section
namespace NND_V2ValidatorTotal
open Aeneas Aeneas.Std Result NND_ResultTotal

theorem zero_binding (b : Array U8 32#usize) : Total (NCX_Reference.required_binding_is_zero b) := by
 unfold NCX_Reference.required_binding_is_zero
 simp only [lift,bind_tc_ok]
 have cap : (Array.to_slice b).val.length ≤ 768 := by
  change b.val.length ≤ 768
  have sz := b.property
  change b.val.length = 32 at sz
  omega
 rw [NHY_NaturalReads.zero _ cap]
 exact pure _

theorem registry (r : NCX_Reference.VerifierRegistryV2) :
 Total (NCX_Reference.validate_verifier_registry_v2 r) := by
 unfold NCX_Reference.validate_verifier_registry_v2
 simp only [lift,bind_tc_ok]
 repeat' first | exact pure _ | split | apply bind _ _ (zero_binding _) | intro

theorem entry (r : NCX_Reference.VerifierRegistryEntryV2) :
 Total (NCX_Reference.validate_verifier_registry_entry_v2 r) := by
 unfold NCX_Reference.validate_verifier_registry_entry_v2
 repeat' first | exact pure _ | split | apply bind _ _ (zero_binding _) | intro

#print axioms zero_binding
#print axioms registry
#print axioms entry
end NND_V2ValidatorTotal
end
