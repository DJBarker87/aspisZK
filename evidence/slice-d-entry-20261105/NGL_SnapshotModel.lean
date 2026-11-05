import NGL_CloneDomain
set_option autoImplicit false
noncomputable section
namespace NGL_SnapshotModel
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Bytes := Slice U8
abbrev V := alloc.vec.Vec U8

/-- Exact owned descriptor construction after the separate SDK borrow reply.
    The copy operation retains allocation failure/divergence, not a free success.
    This is a caller model; the native all-copy/guard/cleanup association is OPEN. -/
def run (copy : Bytes → Result V) (key owner : Key) (signer writable executable : Bool)
    (length1 length2 : Usize) (borrowed : core.result.Result Bytes PE) : Result Account := do
  match borrowed with
  | .Err e => ok ⟨key,owner,signer,writable,executable,.Err e,.Err e⟩
  | .Ok bytes =>
    let n := Slice.len bytes
    if n = length1 ∨ n = length2 then
      let v ← copy bytes
      ok ⟨key,owner,signer,writable,executable,.Ok n,.Ok v⟩
    else ok ⟨key,owner,signer,writable,executable,.Ok n,.Err .InvalidAccountData⟩

/-- Descriptive low-level primitive law already required of to_vec; it says
    nothing about enclosing transaction acceptance or stage outputs. -/
def CopyLengthLaw (copy : Bytes → Result V) : Prop :=
  ∀ bytes v, copy bytes = ok v → v.deref.val.length = bytes.val.length

/-- The approved SDK shared-borrow error characterization, exposed explicitly. -/
def BorrowErrorLaw (borrowed : core.result.Result Bytes PE) : Prop :=
  ∀ e, borrowed = .Err e → e = .AccountBorrowFailed

def Consistent (a : Account) : Prop :=
  (∀ e, a.length = .Err e → e = .AccountBorrowFailed) ∧
  (∀ e, a.bytes = .Err e → e = .AccountBorrowFailed ∨ e = .InvalidAccountData) ∧
  (∀ n v, a.length = .Ok n → a.bytes = .Ok v → n.val = v.deref.val.length)

theorem borrowed_error (copy : Bytes → Result V) (key owner : Key) (s w e : Bool)
    (l1 l2 : Usize) (error : PE) :
    run copy key owner s w e l1 l2 (.Err error) =
      ok ⟨key,owner,s,w,e,.Err error,.Err error⟩ := rfl

theorem rejected_length (copy : Bytes → Result V) (key owner : Key) (s w e : Bool)
    (l1 l2 : Usize) (bytes : Bytes) (bad1 : Slice.len bytes ≠ l1) (bad2 : Slice.len bytes ≠ l2) :
    run copy key owner s w e l1 l2 (.Ok bytes) =
      ok ⟨key,owner,s,w,e,.Ok (Slice.len bytes),.Err .InvalidAccountData⟩ := by
  simp only [run, show ¬ (Slice.len bytes = l1 ∨ Slice.len bytes = l2) from not_or.mpr ⟨bad1,bad2⟩,if_false]

theorem accepted_length (copy : Bytes → Result V) (key owner : Key) (s w e : Bool)
    (l1 l2 : Usize) (bytes : Bytes) (admitted : Slice.len bytes = l1 ∨ Slice.len bytes = l2) :
    run copy key owner s w e l1 l2 (.Ok bytes) =
      (do let v ← copy bytes; ok ⟨key,owner,s,w,e,.Ok (Slice.len bytes),.Ok v⟩) := by
  simp only [run,if_pos admitted]
#print axioms borrowed_error
#print axioms rejected_length
#print axioms accepted_length
end NGL_SnapshotModel
