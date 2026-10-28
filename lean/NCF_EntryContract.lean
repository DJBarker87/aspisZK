import NCC_ReuseAudit
set_option autoImplicit false
noncomputable section
namespace NCF_EntryContract
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1.verifier_registry
local instance : DecidableEq VerifierEntryStatusV1 :=
  fun _ _ => Classical.propDecidable _

/-- Exact typed cohort value paired with NCF's native op29 contract.
This does not identify the enclosing SDK execution or its extraction field. -/
theorem op29_exact (r : VerifierRegistryEntryV2) (slot : U64) :
    NBX_SlotValues.op29 r slot = ok
      (decide (r.status = .Active) && decide (r.activation_slot ≤ slot) &&
       (decide (r.retirement_slot = 18446744073709551615#u64) ||
        decide (slot < r.retirement_slot))) := by
  cases h : r.status <;> simp [NBX_SlotValues.op29, NBX_SlotValues.op30,
    NBX_SlotValues.active, NBX_SlotValues.activeStatus, h]

/-- Exact typed cohort value paired with NCF's native op30 contract. -/
theorem op30_exact (r : VerifierRegistryEntryV1) (slot : U64) :
    NBX_SlotValues.op30 r slot = ok
      (decide (r.status = .Active) && decide (r.activation_slot ≤ slot) &&
       (decide (r.retirement_slot = 18446744073709551615#u64) ||
        decide (slot < r.retirement_slot))) := by
  cases h : r.status <;> simp [NBX_SlotValues.op29, NBX_SlotValues.op30,
    NBX_SlotValues.active, NBX_SlotValues.activeStatus, h]

#print axioms op29_exact
#print axioms op30_exact
end NCF_EntryContract
end
