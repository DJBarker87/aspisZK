import NDH_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDH_RegistrySlots
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry

/-- Free missing slots, with the native scalar reference on the same field.
No statement about the lead's installed dictionary is assumed or changed. -/
def install (base : Ops) : Ops :=
  {base with
    op25 := fun r => NDH_Reference.flag_ref r.flags 2#u8
    op26 := fun r => NDH_Reference.flag_ref r.flags 1#u8
    op27 := fun r => NDH_Reference.flag_ref r.flags 2#u8
    op28 := fun r => NDH_Reference.flag_ref r.flags 1#u8}

theorem immutable_v1 (base : Ops) (r : VerifierRegistryV1) :
    (install base).op25 r = NDH_Reference.flag_ref r.flags 2#u8 := rfl

theorem paused_v1 (base : Ops) (r : VerifierRegistryV1) :
    (install base).op26 r = NDH_Reference.flag_ref r.flags 1#u8 := rfl

theorem immutable_v2 (base : Ops) (r : VerifierRegistryV2) :
    (install base).op27 r = NDH_Reference.flag_ref r.flags 2#u8 := rfl

theorem paused_v2 (base : Ops) (r : VerifierRegistryV2) :
    (install base).op28 r = NDH_Reference.flag_ref r.flags 1#u8 := rfl

theorem digest_preserved (base : Ops) : (install base).op43 = base.op43 := rfl

theorem error_preserved (base : Ops) : (install base).op44 = base.op44 := rfl

#print axioms immutable_v1
#print axioms paused_v1
#print axioms immutable_v2
#print axioms paused_v2
#print axioms digest_preserved
#print axioms error_preserved
end NDH_RegistrySlots
