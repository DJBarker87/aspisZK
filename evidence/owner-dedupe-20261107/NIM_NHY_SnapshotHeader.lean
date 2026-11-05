import NIM_NHY_SnapshotJoin
set_option autoImplicit false
noncomputable section
namespace NHY_SnapshotHeader
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Key := NGL_ReadonlyModel.Key
abbrev Bytes := Slice U8
abbrev Account := NGL_SnapshotModel.Account
inductive Head where
 | copy (bytes : Bytes)
 | done (value : Account)

def header (key owner : Key) (s w x : Bool) (l1 l2 : Usize)
    (borrowed : core.result.Result Bytes PE) : Head :=
 match borrowed with
 | .Err error => .done ⟨key,owner,s,w,x,.Err error,.Err error⟩
 | .Ok bytes =>
   if Slice.len bytes = l1 ∨ Slice.len bytes = l2 then .copy bytes
   else .done ⟨key,owner,s,w,x,.Ok (Slice.len bytes),.Err .InvalidAccountData⟩

def finish (copy : Bytes → Result (alloc.vec.Vec U8))
    (key owner : Key) (s w x : Bool) : Head → Result Account
 | .done value => ok value
 | .copy bytes => do
   let v ← copy bytes
   ok ⟨key,owner,s,w,x,.Ok (Slice.len bytes),.Ok v⟩

/-- Exact before-copy split; no allocation success, final output, or copy value
is an assumption. Both SDK arms and all lengths remain quantified. -/
theorem chain (copy : Bytes → Result (alloc.vec.Vec U8)) (key owner : Key)
    (s w x : Bool) (l1 l2 : Usize) (borrowed : core.result.Result Bytes PE) :
    finish copy key owner s w x (header key owner s w x l1 l2 borrowed) =
      NGL_SnapshotModel.run copy key owner s w x l1 l2 borrowed := by
  cases borrowed with
  | Err error => rfl
  | Ok bytes =>
    by_cases h : Slice.len bytes = l1 ∨ Slice.len bytes = l2
    · simp only [header,if_pos h,finish,NGL_SnapshotModel.run]
    · simp only [header,if_neg h,finish,NGL_SnapshotModel.run]

/-- The exact cloned error supplied by the closed child law. SDK-error branch
establishes its two-error native domain, with no arbitrary String clone. -/
theorem clone_domain :
    NGL_CloneDomain.SnapshotError (AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed) := Or.inl rfl

theorem clone_reply (ops : AdapterRw.Ops) :
    (NGL_CloneDomain.install ops).op35 AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed = ok AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed := rfl

#print axioms chain
#print axioms clone_domain
#print axioms clone_reply
end NHY_SnapshotHeader
