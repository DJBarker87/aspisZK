import LIB_ResultTotal
import NHY_NaturalReads
import NIS_EntryModel
set_option autoImplicit false
noncomputable section
namespace LIB_V2ValidatorTotal
open Aeneas Aeneas.Std Result LIB_ResultTotal

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

theorem zero_binding_value (b : Array U8 32#usize) :
 NCX_Reference.required_binding_is_zero b = ok (decide (b.val = List.replicate 32 0#u8)) := by
 classical
 unfold NCX_Reference.required_binding_is_zero
 simp only [lift,bind_tc_ok]
 have cap : (Array.to_slice b).val.length ≤ 768 := by
  change b.val.length ≤ 768
  have sz := b.property
  change b.val.length = 32 at sz
  omega
 rw [NHY_NaturalReads.zero _ cap]
 apply congrArg Result.ok
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq]
 change (b.val = List.replicate b.val.length 0#u8) ↔ (b.val = List.replicate 32 0#u8)
 rw [b.property]
 rfl

theorem registry (r : NCX_Reference.VerifierRegistryV2) :
 Total (NCX_Reference.validate_verifier_registry_v2 r) := by
 unfold NCX_Reference.validate_verifier_registry_v2
 simp only [lift,bind_tc_ok]
 repeat' first | exact pure _ | split | apply bind _ _ (zero_binding _) | intro

theorem entry (r : NCX_Reference.VerifierRegistryEntryV2) :
 Total (NCX_Reference.validate_verifier_registry_entry_v2 r) := by
 classical
 unfold NCX_Reference.validate_verifier_registry_entry_v2
 simp only [zero_binding_value,bind_tc_ok]
 by_cases hv : r.statement_version = 0#u8
 · simp only [if_pos hv]
   exact pure _
 · simp only [if_neg hv]
   repeat' first | exact pure _ | split

#print axioms zero_binding
#print axioms zero_binding_value
#print axioms registry
#print axioms entry
end LIB_V2ValidatorTotal
end
