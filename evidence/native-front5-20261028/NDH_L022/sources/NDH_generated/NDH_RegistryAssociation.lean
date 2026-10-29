import NDH_RegistrySlots
set_option autoImplicit false
namespace NDH_RegistryAssociation
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry

/-- The missing-slot instance selects the corresponding scalar law on the same
record at the caller. This does not assert that an arbitrary missing adapter
has already been replaced in RPx_Deployed. -/
def immutableAt (ops : Ops) (r1 : VerifierRegistryV1) (r2 : VerifierRegistryV2)
    (version2 : Bool) : Result Bool :=
  if version2 then ops.op28 r2 else ops.op26 r1

def pausedAt (ops : Ops) (r1 : VerifierRegistryV1) (r2 : VerifierRegistryV2)
    (version2 : Bool) : Result Bool :=
  if version2 then ops.op27 r2 else ops.op25 r1

theorem immutable_at_call (base : Ops) (r1 : VerifierRegistryV1)
    (r2 : VerifierRegistryV2) (version2 : Bool) :
    immutableAt (NDH_RegistrySlots.install base) r1 r2 version2 =
      NDH_Reference.flag_ref (if version2 then r2.flags else r1.flags) 2#u8 := by
  cases version2 <;> rfl

theorem paused_at_call (base : Ops) (r1 : VerifierRegistryV1)
    (r2 : VerifierRegistryV2) (version2 : Bool) :
    pausedAt (NDH_RegistrySlots.install base) r1 r2 version2 =
      NDH_Reference.flag_ref (if version2 then r2.flags else r1.flags) 1#u8 := by
  cases version2 <;> rfl

#print axioms immutable_at_call
#print axioms paused_at_call
end NDH_RegistryAssociation
