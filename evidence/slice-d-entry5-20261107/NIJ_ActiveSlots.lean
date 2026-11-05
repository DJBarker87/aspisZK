import NGJ_VERIFIER_IMPORT
import NHY_RegistryPrimitives
set_option autoImplicit false
noncomputable section
namespace NIJ_ActiveSlots
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable
def activeStatus : VerifierEntryStatusV1 → Bool
  | .Active => true
  | _ => false

def active (status : VerifierEntryStatusV1) (activation retirement slot : U64) : Bool :=
  activeStatus status && decide (activation ≤ slot) &&
    (decide (retirement = 18446744073709551615#u64) || decide (slot < retirement))
def op29 (r : VerifierRegistryEntryV2) (slot : U64) : Result Bool :=
  ok (active r.status r.activation_slot r.retirement_slot slot)
def op30 (r : VerifierRegistryEntryV1) (slot : U64) : Result Bool :=
  ok (active r.status r.activation_slot r.retirement_slot slot)


def install (base : AdapterRw.Ops) : AdapterRw.Ops :=
 {base with op29:=op29,op30:=op30}
theorem op29_exact (r : VerifierRegistryEntryV2) (slot : U64) :
    NIJ_ActiveSlots.op29 r slot = ok
      (decide (r.status = .Active) && decide (r.activation_slot ≤ slot) &&
       (decide (r.retirement_slot = 18446744073709551615#u64) ||
        decide (slot < r.retirement_slot))) := by
  cases h : r.status <;> simp [NIJ_ActiveSlots.op29, NIJ_ActiveSlots.op30,
    NIJ_ActiveSlots.active, NIJ_ActiveSlots.activeStatus, h]

/-- Exact typed cohort value paired with NCF's native op30 contract. -/
theorem op30_exact (r : VerifierRegistryEntryV1) (slot : U64) :
    NIJ_ActiveSlots.op30 r slot = ok
      (decide (r.status = .Active) && decide (r.activation_slot ≤ slot) &&
       (decide (r.retirement_slot = 18446744073709551615#u64) ||
        decide (slot < r.retirement_slot))) := by
  cases h : r.status <;> simp [NIJ_ActiveSlots.op29, NIJ_ActiveSlots.op30,
    NIJ_ActiveSlots.active, NIJ_ActiveSlots.activeStatus, h]

theorem selected (base : AdapterRw.Ops) :
 (install base).op29=op29 ∧ (install base).op30=op30 := ⟨rfl,rfl⟩

theorem digest_error_frame (base : AdapterRw.Ops) :
 (install base).op43=base.op43 ∧ (install base).op44=base.op44 := ⟨rfl,rfl⟩
theorem retirement_v1 (r : VerifierRegistryEntryV1) (slot : U64) :
 op30 r slot=match r.status with
 | .Active => if r.activation_slot≤slot then do
    let noRetirement ← NHY_RegistryPrimitives.noRetirementV1 r
    ok (noRetirement || decide (slot<r.retirement_slot))
   else ok false
 | _ => ok false := by
 have max : core.num.U64.MAX = 18446744073709551615#u64 := by rfl
 cases h : r.status <;>
  simp [op30,active,activeStatus,h,NHY_RegistryPrimitives.noRetirementV1,
   NHY_RegistryReference.retirement_ref,max]
 all_goals split <;> simp_all

theorem retirement_v2 (r : VerifierRegistryEntryV2) (slot : U64) :
 op29 r slot=match r.status with
 | .Active => if r.activation_slot≤slot then do
    let noRetirement ← NHY_RegistryPrimitives.noRetirementV2 r
    ok (noRetirement || decide (slot<r.retirement_slot))
   else ok false
 | _ => ok false := by
 have max : core.num.U64.MAX = 18446744073709551615#u64 := by rfl
 cases h : r.status <;>
  simp [op29,active,activeStatus,h,NHY_RegistryPrimitives.noRetirementV2,
   NHY_RegistryReference.retirement_ref,max]
 all_goals split <;> simp_all

#print axioms op29_exact
#print axioms op30_exact
#print axioms selected
#print axioms digest_error_frame
#print axioms retirement_v1
#print axioms retirement_v2
end NIJ_ActiveSlots
