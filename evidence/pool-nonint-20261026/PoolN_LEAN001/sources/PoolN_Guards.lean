import Hiq_PoolGuards
set_option autoImplicit false
namespace AspisR1.PoolN_Guards
open Aeneas Aeneas.Std

/-- Guard-level control model, not an unproved whole-handler specification.
Native P6 checks in PoolN_KANI test the corresponding literal guards and errors.
Metadata uses the existing SDK account carrier. Bytes are not replaced by hashes. -/
structure Account where
  meta : AdapterRw.Cuts.Account
  data : List U8

abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

def invalidFresh : Error := .Custom 1095966773#u32

def invalidType : Error := .Custom 1095966721#u32

/-- Literal metadata and size prefix of require_prepared_plan_account_v1. -/
noncomputable def prepared (a : Account) (id : Key) (size : Nat) : Except Error Unit := by
  classical
  exact if a.meta.owner ≠ id ∨ a.meta.executable = true ∨ a.meta.is_signer = true ∨
      a.meta.is_writable = false ∨ a.data.length ≠ size
    then .error .InvalidAccountData else .ok ()

/-- Length branch of validate_root_page_bytes, before any indexed read. -/
def pageLength (bytes : List U8) : Except Error Unit :=
  if bytes.length != 8256 then .error invalidType else .ok ()

/-- An occupied ASC8 needs no byte enumeration for another role's size test. -/
def CheckpointLength (a : Account) : Prop := a.data.length = 192 ∨ a.data.length = 1768

/-- Actual non-checkpoint destination sizes: master, lane, legacy state, page,
core plan, rollover plan and nullifier marker. The marker size is audited
separately against source; it is not inferred from this list. -/
def OtherSize (size : Nat) : Prop :=
  size = 384 ∨ size = 768 ∨ size = 1000 ∨ size = 8256 ∨ size = 10000 ∨ size = 8504

theorem different_size (a : Account) (size : Nat) (cp : CheckpointLength a)
    (other : OtherSize size) : a.data.length ≠ size := by
  rcases cp with cp | cp <;>
    rcases other with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem prepared_rejects (a : Account) (id : Key) (size : Nat)
    (cp : CheckpointLength a) (plan : size = 10000 ∨ size = 8504) :
    prepared a id size = .error .InvalidAccountData := by
  have different := different_size a size cp (by rcases plan with h | h <;> simp [OtherSize,h])
  simp [prepared,different]

theorem page_rejects (bytes : List U8) (cp : bytes.length = 192 ∨ bytes.length = 1768) :
    pageLength bytes = .error invalidType := by
  have different : bytes.length ≠ 8256 := by rcases cp with h | h <;> omega
  simp [pageLength,different]

#print axioms different_size
#print axioms prepared_rejects
#print axioms page_rejects
end AspisR1.PoolN_Guards
