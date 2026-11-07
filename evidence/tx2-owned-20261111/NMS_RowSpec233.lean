import NMS_OwnedPackets
import NLM_Auth233
import NLM_DeployedOps
set_option autoImplicit false
noncomputable section
namespace NMS_RowSpec233
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets
structure Args where
 program : solana_pubkey.Pubkey
 accounts : Slice r1_pool_adapter.owned.OwnedAccount
 pool : solana_pubkey.Pubkey
 lane : U8
 slot : U64
/-- World is the complete external account/counter/return-data/ambient frame.
Owned-only233 does not borrow an SDK cell or write this frame. -/
abbrev World := NLM_PacketTypes.World
abbrev Event := NLM_Auth233.Event
abbrev Outcome (W : Type) := End W Event Auth
abbrev Native (Ambient : Type) := Args → World Ambient → Outcome (World Ambient)
/-- The actual child law includes the complete Result, exact source chronology,
all four boxed payloads/owners on success, the immutable external frame on
returns, and only an ordered prefix on stops. Pure allocator internals and pure
cleanup are outside the obligation under(bl)(3). Freshness is nominal ownership,
not an assumed physical allocation or an endpoint-equality premise in a root. -/
def Law {Ambient : Type} (inputOwners : List Nat) (before : World Ambient)
 (source : NJU_Log.Run Event (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE))
 : Outcome (World Ambient) → Prop
 | .returned (.Ok auth) post events =>
   source.result = .ok (.Ok auth.erase) ∧ events = source.events ∧
   post = before ∧ auth.Fresh inputOwners
 | .returned (.Err error) post events =>
   source.result = .ok (.Err error) ∧ events = source.events ∧ post = before
 | .stopped events (.failed error) =>
   source.result = .fail error ∧ events = source.events
 | .stopped events .diverged => source.result = .div ∧ events = source.events
def eraseValue {Ambient : Type} (e : Outcome (World Ambient)) :
 Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE) :=
 match e.value with
 | .ok (.Ok auth) => .ok (.Ok auth.erase)
 | .ok (.Err error) => .ok (.Err error)
 | .fail error => .fail error
 | .div => .div
/-- Full-strength OPEN233 packet at the ORIGINAL arguments and the fixed
headline SDK installation. No free Ops dictionary is accepted here. The parent
may assume this named RowSpec only in its parameterized fold, never as a root. -/
def RowSpec_233 {Ambient CoreError : Type}
 (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
 (reservation : AspisR1.NP6_StdModel.Reservation)
 (inputOwners : Args → List Nat) (native : Native Ambient) : Prop :=
 ∀ a before, Law (inputOwners a) before
  (NLM_Auth233.G (NLM_DeployedOps.ops missing indexError reservation)
   a.program a.accounts a.pool a.lane a.slot) (native a before) ∧
 eraseValue (native a before) =
  r1_pool_adapter.owned.authenticate_asq8_accounts
   (NLM_DeployedOps.ops missing indexError reservation)
   a.program a.accounts a.pool a.lane a.slot

/-- A successful packet identifies every returned boxed payload; owner
freshness remains attached to this SAME reply rather than another witness. -/
theorem successful {Ambient : Type} (owners : List Nat) (before post : World Ambient)
 (source : NJU_Log.Run Event (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE))
 (auth : Auth) (events : List Event)
 (law : Law owners before source (.returned (.Ok auth) post events)) :
 source.result = .ok (.Ok auth.erase) ∧ auth.Fresh owners ∧ post = before :=
 ⟨law.1,law.2.2.2,law.2.2.1⟩
#print RowSpec_233
#print axioms successful
end NMS_RowSpec233
