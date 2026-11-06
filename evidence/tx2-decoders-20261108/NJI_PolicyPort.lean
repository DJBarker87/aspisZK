import NJI_Extracted.Core
import NHY_PolicyModel
set_option autoImplicit false
noncomputable section
namespace NJI_PolicyPort
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev P := NJI_Extracted.aspis_statement.pool_v1.format.VerifierPolicyV1
abbrev F := NJI_Extracted.aspis_statement.pool_v1.format.PoolV1FormatError
abbrev CP := AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1
abbrev CF := AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError
def error : F → CF
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .NonZeroReserved => .NonZeroReserved
 | .NonCanonicalAssetId => .NonCanonicalAssetId
 | .UnsupportedFlags => .UnsupportedFlags
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidAuthorityMode => .InvalidAuthorityMode

def from_error : CF → F
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .NonZeroReserved => .NonZeroReserved
 | .NonCanonicalAssetId => .NonCanonicalAssetId
 | .UnsupportedFlags => .UnsupportedFlags
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidAuthorityMode => .InvalidAuthorityMode

def policy (p : P) : CP := ⟨p.flags,p.registry_program,p.registry_authority,p.policy_binding⟩
def from_policy (p : CP) : P := ⟨p.flags,p.registry_program,p.registry_authority,p.policy_binding⟩
def unport (r : core.result.Result Unit CF) : core.result.Result Unit F :=
 match r with | .Ok u => .Ok u | .Err e => .Err (from_error e)
def validator (p : P) : Result (core.result.Result Unit F) := do
 let reply ← NHY_PolicyModel.policy (policy p)
 ok (unport reply)

theorem policy_roundtrip (p : P) : from_policy (policy p)=p := by cases p;rfl
theorem policy_surjective (p : CP) : policy (from_policy p)=p := by cases p;rfl
theorem error_roundtrip (e : F) : from_error (error e)=e := by cases e <;> rfl

/-- Same exact decoded record is supplied to the already CLOSED op15 law. -/
theorem validator_value (p : P) : validator p = ok (unport (NHY_PolicyModel.decode
 (NHY_PolicyModel.code p.flags
  (decide (p.registry_program=Array.repeat 32#usize 0#u8))
  (decide (p.registry_authority=Array.repeat 32#usize 0#u8))
  (decide (p.policy_binding=Array.repeat 32#usize 0#u8))))) := by
 unfold validator
 rw [NHY_PolicyModel.value]
 rfl
#print axioms policy_roundtrip
#print axioms policy_surjective
#print axioms error_roundtrip
#print axioms validator_value
end NJI_PolicyPort
