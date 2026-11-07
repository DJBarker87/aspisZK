import NLM_DeployedOps
import NLM_PacketTypes
import NLE_OwnedState
set_option autoImplicit false
noncomputable section
namespace NMN_242Interface
open Aeneas Aeneas.Std Result AdapterRw AspisR1
/-- Exact source argument types of validate_asq8, not a scalar ABI summary. -/
structure Args where
 program : solana_pubkey.Pubkey
 accounts : Slice r1_pool_adapter.owned.OwnedAccount
 data : Slice U8
 slot : core.result.Result U64 solana_program_error.ProgramError
/-- ValidatedAsqa retains the entire statement and proof_length. The Box is
fresh allocator-owned storage under (bl)(3); its statement value is not erased. -/
abbrev Reply := core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError
/-- A stopped arm has only its ordered prefix and pending event. No post-world,
returned value, cleanup state or suffix is invented. Event is an explicit
future canonical242 observable carrier, not an admitted weaker draft packet. -/
inductive End (Ambient Event Pending : Type) where
 | returned (reply : Result Reply) (world : NLM_PacketTypes.World Ambient) (events : List Event)
 | stopped (events : List Event) (pending : Pending)
/-- Result projection only; this is explicitly NOT a full242 RowSpec. The full
observable source law is still an OPEN parameter of any future241 fold. -/
def SourceValue {CoreError : Type} (missing : AspisR1.IDa_Deployed.Uninstalled CoreError)
 (indexError : CoreError) (reservation : NP6_StdModel.Reservation)
 (a : Args) : Result Reply :=
 r1_pool_adapter.owned.validate_asq8 (NLM_DeployedOps.ops missing indexError reservation)
  a.program a.accounts a.data a.slot
#print Args
#print Reply
#print End
#print SourceValue
end NMN_242Interface
