import NLF_Drop
set_option autoImplicit false
namespace NLF_SdkModel
open NLF_RefCell
structure Account where
  key : List UInt8
  owner : List UInt8
  data : Nat
  lamports : Nat
  signer : Bool
  writable : Bool
  executable : Bool
  rentEpoch : Nat
structure Payload where
  bytes : List UInt8
  money : Nat
  deriving DecidableEq
structure State where
  accounts : Nat → Account
  cells : Nat → Cell Payload
inductive ProgramError where | accountBorrowFailed deriving DecidableEq

def put (s : State) (i : Nat) (c : Cell Payload) : State :=
  {s with cells := fun j => if j = i then c else s.cells j}

def wrap (s : State) (i t : Nat) (k : Kind) : State × Except ProgramError Guard :=
  match (match k with | .shared => shared (s.cells i) t | .exclusive => exclusive (s.cells i) t) with
  | .error _ => (s, .error .accountBorrowFailed)
  | .ok c => (put s i c, .ok ⟨i,t,k⟩)

def try_borrow_data (s : State) (a t : Nat) := wrap s (s.accounts a).data t .shared
def try_borrow_mut_data (s : State) (a t : Nat) := wrap s (s.accounts a).data t .exclusive
def try_borrow_lamports (s : State) (a t : Nat) := wrap s (s.accounts a).lamports t .shared
def try_borrow_mut_lamports (s : State) (a t : Nat) := wrap s (s.accounts a).lamports t .exclusive

def deref (s : State) (g : Guard) : Payload := (s.cells g.cell).payload

def release (s : State) (g : Guard) : Except Error State :=
  match (match g.kind with
    | .shared => dropShared (s.cells g.cell) g.token
    | .exclusive => dropExclusive (s.cells g.cell) g.token) with
  | .error e => .error e
  | .ok c => .ok (put s g.cell c)

/-- Exact short-lived shared borrow: Err is returned, and the success guard is
released before the scalar is returned. Panic getters map Err to abort (none). -/
def scalar (s : State) (i t : Nat) (f : Payload → Nat) : State × Except ProgramError Nat :=
  match wrap s i t .shared with
  | (s', .error e) => (s', .error e)
  | (s', .ok g) =>
    match release s' g with
    | .ok s'' => (s'', .ok (f (deref s' g)))
    | .error _ => (s', .error .accountBorrowFailed)

def try_data_len (s : State) (a t : Nat) := scalar s (s.accounts a).data t (fun p => p.bytes.length)
def try_lamports (s : State) (a t : Nat) := scalar s (s.accounts a).lamports t Payload.money

def data_len (s : State) (a t : Nat) : Option (State × Nat) :=
  match try_data_len s a t with | (s', .ok n) => some (s',n) | _ => none

def lamports (s : State) (a t : Nat) : Option (State × Nat) :=
  match try_lamports s a t with | (s', .ok n) => some (s',n) | _ => none

def unsigned_key (s : State) (a : Nat) := (s.accounts a).key
def owner (s : State) (a : Nat) := (s.accounts a).owner

theorem put_same (s : State) (i : Nat) (c : Cell Payload) : (put s i c).cells i = c := by simp [put]
theorem put_other (s : State) (i j : Nat) (c : Cell Payload) (h : j ≠ i) :
    (put s i c).cells j = s.cells j := by simp [put, h]
theorem put_restore (s : State) (i : Nat) (c : Cell Payload) :
    put (put s i c) i (s.cells i) = s := by
  cases s; simp only [put]; congr; funext j; split_ifs <;> simp_all

theorem wrapper_error (s : State) (i t : Nat) (k : Kind)
    (h : (match k with | .shared => shared (s.cells i) t | .exclusive => exclusive (s.cells i) t) = .error .conflict) :
    wrap s i t k = (s,.error .accountBorrowFailed) := by simp [wrap, h]

theorem wrapper_frame (s : State) (i t : Nat) (k : Kind) :
    (wrap s i t k).1.accounts = s.accounts := by
  unfold wrap; split <;> rfl

#print axioms put_same
#print axioms put_other
#print axioms put_restore
#print axioms wrapper_error
#print axioms wrapper_frame
end NLF_SdkModel
