import NHJ_CheckpointPacket
set_option autoImplicit false
namespace NHJ_GuardPacket
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev R := core.result.Result Unit PE
structure Reply where
  success : Bool
  borrow : Bool

def error (stage : Nat) (borrow : Bool) : PE :=
  if stage = 1 ∧ borrow then .AccountBorrowFailed
  else if stage = 5 then .InvalidArgument else .InvalidAccountData

def decode (stage : Nat) (reply : Reply) : R :=
  if reply.success then .Ok () else .Err (error stage reply.borrow)

def encode : R → Reply
  | .Ok _ => ⟨true,false⟩
  | .Err e => ⟨false,match e with | .AccountBorrowFailed => true | _ => false⟩

def Domain (stage : Nat) : R → Prop
  | .Ok _ => True
  | .Err e => e = error stage false ∨ e = error stage true

theorem decode_encode (stage : Nat) (reply : R) (domain : Domain stage reply) :
    decode stage (encode reply) = reply := by
  cases reply with
  | Ok value => cases value; rfl
  | Err e =>
    rcases domain with rfl | rfl
    · by_cases one : stage=1 <;> by_cases five : stage=5 <;>
        simp [decode,encode,error,one,five]
    · by_cases one : stage=1 <;> by_cases five : stage=5 <;>
        simp [decode,encode,error,one,five]

/-- Explicit first-error continuation, with one log entry for every executed
callee and no log for its unexecuted suffix. -/
def run : List R → List R × R
  | [] => ([],.Ok ())
  | first::rest => match first with
    | .Err e => ([first],.Err e)
    | .Ok _ => let tail := run rest; (first::tail.1,tail.2)

theorem first_error (earlier : List R) (successful : ∀ r ∈ earlier, r = .Ok ())
    (e : PE) (suffix : List R) :
    run (earlier ++ .Err e :: suffix) = (earlier ++ [.Err e],.Err e) := by
  induction earlier with
  | nil => rfl
  | cons first rest ih =>
    have firstOk := successful first (by simp)
    subst first
    have restOk : ∀ r ∈ rest, r = .Ok () := by
      intro r member
      exact successful r (by simp [member])
    simpa [run,List.cons_append,ih restOk]

theorem complete (replies : List R) (successful : ∀ r ∈ replies, r = .Ok ()) :
    run replies = (replies,.Ok ()) := by
  induction replies with
  | nil => rfl
  | cons first rest ih =>
    have firstOk := successful first (by simp)
    subst first
    have restOk : ∀ r ∈ rest, r = .Ok () := by
      intro r member
      exact successful r (by simp [member])
    simpa [run,ih restOk]
#print axioms decode_encode
#print axioms first_error
#print axioms complete
end NHJ_GuardPacket
