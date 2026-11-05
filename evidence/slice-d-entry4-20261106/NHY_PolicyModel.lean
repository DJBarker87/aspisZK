import NHY_PolicyReference
import NHJ_DeployedIds
set_option autoImplicit false
noncomputable section
namespace NHY_PolicyModel
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Policy := AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1
abbrev Error := AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError

def code (flags : U8) (program_zero authority_zero binding_zero : Bool) : U8 :=
 if flags &&& (~~~ 3#u8) != 0#u8 then 1#u8
 else if program_zero || binding_zero then 2#u8
 else
  let immutable := flags &&& 1#u8 != 0#u8
  let deployment := flags &&& 2#u8 != 0#u8
  if deployment && !immutable then 3#u8
  else if immutable != authority_zero then 3#u8 else 0#u8

theorem extracted (flags : U8) (pz az bz : Bool) :
    NHY_PolicyReference.policy_ref flags pz az bz = ok (code flags pz az bz) := by
  simp only [NHY_PolicyReference.policy_ref,code,lift,bind_tc_ok]
  generalize (flags &&& (~~~ 3#u8) != 0#u8) = bad
  generalize (flags &&& 1#u8 != 0#u8) = immutable
  generalize (flags &&& 2#u8 != 0#u8) = deployment
  cases bad <;> cases immutable <;> cases deployment <;>
    cases pz <;> cases az <;> cases bz <;> rfl

def decode (c : U8) : core.result.Result Unit Error :=
 if c=0#u8 then .Ok () else
 if c=1#u8 then .Err .UnsupportedFlags else
 if c=2#u8 then .Err .ZeroRequiredBinding else .Err .InvalidAuthorityMode

def policy (p : Policy) : Result (core.result.Result Unit Error) := do
 let c ← NHY_PolicyReference.policy_ref p.flags
   (decide (p.registry_program = Array.repeat 32#usize 0#u8))
   (decide (p.registry_authority = Array.repeat 32#usize 0#u8))
   (decide (p.policy_binding = Array.repeat 32#usize 0#u8))
 ok (decode c)

theorem value (p : Policy) : policy p = ok (decode (code p.flags
    (decide (p.registry_program = Array.repeat 32#usize 0#u8))
    (decide (p.registry_authority = Array.repeat 32#usize 0#u8))
    (decide (p.policy_binding = Array.repeat 32#usize 0#u8)))) := by
 unfold policy
 rw [extracted]
 rfl

/-- Bind this concrete helper in the real deployed pipeline; other fields are
unchanged. Native source/contract provenance is a separate P6 certificate. -/
def bindPolicy {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
 {missing with adapter := {missing.adapter with op15 := policy}}

theorem actual_slot {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (NHJ_DeployedIds.configuration (bindPolicy missing) devnet indexError reservation).adapter.op15 = policy := rfl

#print axioms extracted
#print axioms value
#print axioms actual_slot
end NHY_PolicyModel
