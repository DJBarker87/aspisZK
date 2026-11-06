import NFU_AdapterGetters
set_option autoImplicit false
noncomputable section
namespace NJD_GuardCuts
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Reply := core.result.Result Unit PE

/-- Source-ordered guard continuation: no child-success premise. -/
def step (r : Reply) : Reply := match r with
  | .Ok _ => .Ok ()
  | .Err e => .Err e

def readonlyReply (a : Account) : Reply :=
  if a.is_signer || a.is_writable || a.executable then .Err .InvalidAccountData else .Ok ()

/-- Only the fields actually asserted by NJD_guards.patch run are present.
Native account/owner pointers decode to handles; they do not imply payload equality.
Native cases have deferred bytes, so this is NOT a full-account native frame. -/
structure Log where
  accountHandle : Nat
  ownerHandle : Nat
  writable : Bool
  calls : Nat
  failed : Bool
  kind : Nat

def metadataFrame (keyByte : Key → Fin 32 → U8) (index : Fin 32)
    (before after : Account) : Prop :=
  keyByte after.key index = keyByte before.key index ∧
  keyByte after.owner index = keyByte before.owner index ∧
  after.is_signer = before.is_signer ∧ after.is_writable = before.is_writable ∧
  after.executable = before.executable ∧ after.length = before.length

def cut (accountHandle ownerHandle kind : Nat) (writable : Bool)
    (keyByte : Key → Fin 32 → U8) (index : Fin 32)
    (before after : Account) (returned logged : Reply) (log : Log) : Prop :=
  returned = logged ∧ log.accountHandle = accountHandle ∧ log.ownerHandle = ownerHandle ∧
  log.writable = writable ∧ log.kind = kind ∧ log.calls = 1 ∧
  log.failed = (match returned with | .Ok _ => false | .Err _ => true) ∧
  metadataFrame keyByte index before after

/-- Complete Result association for the guard's actual try continuation. -/
theorem step_result (r : Reply) : step r = r := by cases r <;> rfl

/-- Reuse the CLOSED metadata child on every full Account; bytes are unread.
This mathematical extension is separate from the restricted native harness. -/
theorem readonly_source (a : Account) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer a = ok (readonlyReply a) := by
  change AdapterRw.r1_pool_adapter.readonly_buffer_meta_ok
    a.is_signer a.is_writable a.executable = _
  unfold AdapterRw.r1_pool_adapter.readonly_buffer_meta_ok readonlyReply
  cases hs : a.is_signer <;> cases hw : a.is_writable <;> cases he : a.executable <;> simp [hs,hw,he]

/-- Every arm substituted from the CLOSED child, including its rejecting arm. -/
theorem readonly_step (a : Account) :
    (do let r ← AdapterRw.r1_pool_adapter.owned.require_readonly_buffer a
        ok (step r)) = ok (readonlyReply a) := by
  rw [readonly_source]
  simp only [bind_tc_ok, step_result]

/-- A chain consumes each actual logged reply in order; errors stop its suffix. -/
def chain : List Reply → Reply
  | [] => .Ok ()
  | r::rs => match r with | .Err e => .Err e | .Ok _ => chain rs

theorem chain_error (e : PE) (later : List Reply) : chain (.Err e::later) = .Err e := rfl

theorem chain_continue (later : List Reply) : chain (.Ok ()::later) = chain later := rfl

/-- Readonly full-record irrelevance follows from the CLOSED source law, not
from pointer equality or the native metadata-only frame. -/
theorem readonly_bytes_irrelevant (a b : Account)
    (s : a.is_signer = b.is_signer) (w : a.is_writable = b.is_writable)
    (e : a.executable = b.executable) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer a =
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer b :=
  NFU_AdapterGetters.readonly_frame a b s w e

#print axioms step_result
#print axioms readonly_source
#print axioms readonly_step
#print axioms chain_error
#print axioms chain_continue
#print axioms readonly_bytes_irrelevant
end NJD_GuardCuts
end
