import NDH_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NDH_PolicySlot
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.format

/-- Array equality is by the same 32 byte values. Native equality is checked
under KMX; the result code preserves the actual native error alternatives. -/
def zero32 (a : Array U8 32#usize) : Bool :=
  decide (a.val = List.replicate 32 0#u8)

def liftCode (code : U8) : core.result.Result Unit PoolV1FormatError :=
  if code=0#u8 then .Ok () else
  if code=1#u8 then .Err .UnsupportedFlags else
  if code=2#u8 then .Err .ZeroRequiredBinding else .Err .InvalidAuthorityMode

def policy (r : VerifierPolicyV1) :
    Result (core.result.Result Unit PoolV1FormatError) := do
  let code ← NDH_Reference.policy_ref r.flags (zero32 r.registry_program)
    (zero32 r.registry_authority) (zero32 r.policy_binding)
  ok (liftCode code)

def install (base : Ops) : Ops := {base with op15 := policy}

theorem at_call (base : Ops) (r : VerifierPolicyV1) :
    (install base).op15 r = policy r := rfl

theorem preserves_digest (base : Ops) : (install base).op43 = base.op43 := rfl

#print axioms at_call
#print axioms preserves_digest
end NDH_PolicySlot
