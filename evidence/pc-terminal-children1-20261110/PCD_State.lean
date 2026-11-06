import PCD_Error
import NLF_ParentModel
set_option autoImplicit false
namespace PCD
abbrev Bytes := List UInt8
abbrev Key := Vector UInt8 32
structure Meta where
  key : Key
  signer : Bool
  writable : Bool
  deriving DecidableEq
structure Instruction where
  program : Key
  metas : List Meta
  data : Bytes
  deriving DecidableEq
structure Invocation where
  instruction : Instruction
  infos : List Nat
  deriving DecidableEq
structure CellView where
  data : Bytes
  lamports : UInt64
  owner : Key
  deriving DecidableEq
/-- This is the return-register projection; it never stands for the whole heap. -/
abbrev Register := Option (Key × Bytes)
structure State where
  loans : NLF_ParentModel.Parent
  views : Nat → CellView
  register : Register
  cpiHistory : List Invocation
inductive Event where
  | child (row : Nat)
  | allocate (block : Nat)
  | clear
  | invoke (invocation : Invocation)
  | read (reply : Register)
  | borrow (cell token : Nat)
  | release (cell token : Nat)
  deriving DecidableEq
structure Execution (α : Type) where
  reply : Exit α
  state : State
  events : List Event

/-- Retains complete Err, abort, divergence, same state and exact prefix. -/
def bind {α β : Type} (first : Execution α) (next : α → State → Execution β) : Execution β :=
  match first.reply with
  | .ok a =>
    let rest := next a first.state
    ⟨rest.reply, rest.state, first.events ++ rest.events⟩
  | .error e => ⟨.error e, first.state, first.events⟩
  | .abort => ⟨.abort, first.state, first.events⟩
  | .diverge => ⟨.diverge, first.state, first.events⟩
end PCD
