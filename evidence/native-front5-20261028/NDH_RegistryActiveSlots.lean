import NDH_RegistryPrimitives
set_option autoImplicit false
namespace NDH_RegistryActiveSlots
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry

/-- A representation at the free active-at-slot boundaries. This supplies
local helper call sites; no native proof of the whole parent is asserted. -/
def activeV1 (r : VerifierRegistryEntryV1) (slot : U64) : Result Bool :=
  match r.status with
  | .Active => if r.activation_slot≤slot then do
      let noRetirement ← NDH_RegistryPrimitives.noRetirementV1 r
      ok (noRetirement || decide (slot<r.retirement_slot))
    else ok false
  | _ => ok false

def activeV2 (r : VerifierRegistryEntryV2) (slot : U64) : Result Bool :=
  match r.status with
  | .Active => if r.activation_slot≤slot then do
      let noRetirement ← NDH_RegistryPrimitives.noRetirementV2 r
      ok (noRetirement || decide (slot<r.retirement_slot))
    else ok false
  | _ => ok false

def install (base : Ops) : Ops := {base with op29:=activeV2,op30:=activeV1}

theorem v1_call (base : Ops) (r : VerifierRegistryEntryV1) (slot : U64) :
    (install base).op30 r slot =
      match r.status with
      | .Active => if r.activation_slot≤slot then do
          let noRetirement ← NDH_Reference.retirement_ref r.retirement_slot
          ok (noRetirement || decide (slot<r.retirement_slot))
        else ok false
      | _ => ok false := rfl

theorem v2_call (base : Ops) (r : VerifierRegistryEntryV2) (slot : U64) :
    (install base).op29 r slot =
      match r.status with
      | .Active => if r.activation_slot≤slot then do
          let noRetirement ← NDH_Reference.retirement_ref r.retirement_slot
          ok (noRetirement || decide (slot<r.retirement_slot))
        else ok false
      | _ => ok false := rfl

#print axioms v1_call
#print axioms v2_call
end NDH_RegistryActiveSlots
