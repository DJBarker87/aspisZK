import AdapterRwTypes

/-! Mechanical native snapshot emission, with external SDK carriers/operations
as parameters. No SDK interpretation or native heap-frame instance is asserted.
Aeneas erases implicit drops; their runtime join is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W.Snapshot
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev OwnedAccount := AdapterRw.r1_pool_adapter.owned.OwnedAccount

structure Carriers where
  RefCell : Type → Type
  Ref : Type → Type
  Rc : Type → Type

structure AccountInfo (C : Carriers) where
  key : AdapterRw.solana_pubkey.Pubkey
  lamports : C.Rc (C.RefCell U64)
  data : C.Rc (C.RefCell (Slice U8))
  owner : AdapterRw.solana_pubkey.Pubkey
  rent_epoch : U64
  is_signer : Bool
  is_writable : Bool
  executable : Bool

structure Ops (C : Carriers) where
  borrow : AccountInfo C → Result ((core.result.Result (C.Ref (Slice U8)) PE) ×
    (core.result.Result (C.Ref (Slice U8)) PE → Unit))
  deref : C.Ref (Slice U8) → Result (Slice U8)
  cloneError : PE → Result PE

def snapshot (C : Carriers) (ops : Ops C)
  (account : AccountInfo C) (length1 : Std.Usize)
  (length2 : Std.Usize) :
  Result OwnedAccount
  := do
  let (r, _) ← ops.borrow account
  match r with
  | core.result.Result.Ok data =>
    let s ← ops.deref data
    let length := Slice.len s
    if length = length1
    then
      let v ← alloc.slice.Slice.to_vec core.clone.CloneU8 s
      ok
        {
          key := account.key,
          owner := account.owner,
          is_signer := account.is_signer,
          is_writable := account.is_writable,
          executable := account.executable,
          length := (core.result.Result.Ok length),
          bytes := (core.result.Result.Ok v)
        }
    else
      if length = length2
      then
        let v ← alloc.slice.Slice.to_vec core.clone.CloneU8 s
        ok
          {
            key := account.key,
            owner := account.owner,
            is_signer := account.is_signer,
            is_writable := account.is_writable,
            executable := account.executable,
            length := (core.result.Result.Ok length),
            bytes := (core.result.Result.Ok v)
          }
      else
        ok
          {
            key := account.key,
            owner := account.owner,
            is_signer := account.is_signer,
            is_writable := account.is_writable,
            executable := account.executable,
            length := (core.result.Result.Ok length),
            bytes :=
              (core.result.Result.Err
                AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
          }
  | core.result.Result.Err error =>
    let pe ←
      ops.cloneError error
    ok
      {
        key := account.key,
        owner := account.owner,
        is_signer := account.is_signer,
        is_writable := account.is_writable,
        executable := account.executable,
        length := (core.result.Result.Err pe),
        bytes := (core.result.Result.Err error)
      }

#print axioms snapshot
end AspisR1.S2W.Snapshot
end
