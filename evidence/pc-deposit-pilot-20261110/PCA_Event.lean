import PCA_State
set_option autoImplicit false
namespace PCA
/-- Typed arguments of every source callee. A site is its frozen source line;
repeated calls remain different occurrences even when their arguments agree. -/
inductive Call : Type → Type where
  | decode (bytes : Bytes) : Call Request
  | accountGet (index : Nat) : Call Nat
  | master (program : Key) (account : Nat) : Call Master
  | commitment (owner : Digest) (amount : UInt32) (asset : UInt32) (salt : Digest) : Call Digest
  | laneId (commitment : Digest) : Call UInt8
  | lane (program : Key) (master : Bytes) (laneId : UInt8) (account : Nat) : Call Lane
  | singleOutput (commitment : Digest) : Call (Vector (UInt32 × Digest) 2)
  | leafDigest (witness : Vector (UInt32 × Digest) 2) : Call Digest
  | prepare (lane : Lane) (laneId : UInt8) (leaf : Digest) : Call (Append × Vector UInt8 768)
  | location (sequence : UInt64) : Call Location
  | empty (account : Nat) : Call Bool
  | zeroed (account : Nat) (program : Key) : Call Bool
  | pageAddress (program : Key) (lane : Bytes) (page : UInt64) : Call (Key × UInt8)
  | freshPda (account : Nat) (program expected : Key) (bytes : Nat) : Call Preparation
  | currentPage (program : Key) (laneAccount pageAccount : Nat) (lane : Lane)
      (requireRoom : Bool) (hint : Option UInt8) : Call Header
  | exactCount (count : Nat) : Call Unit
  | unique : Call Unit
  | tokenProgram (account : Nat) : Call Unit
  | transfer (program : Key) (master : Bytes) (identity : Identity)
      (accounts : List Nat) (amount : UInt32) : Call TransferPlan
  | transferInfos (accounts : List Nat) : Call (Vector Nat 5)
  | payerSystem (payer system : Nat) : Call Unit
  | createPda (payer account system bytes : Nat) (owner : Key) (seeds : List Bytes) : Call Unit
  | ownedZeroed (account : Nat) (program : Key) (bytes : Nat) (rent : Rent) : Call Unit
  | invoke (instruction : Instruction) (infos : Vector Nat 5) : Call Unit
  | delta (accounts : List Nat) (plan : TransferPlan) : Call Unit
  | writePage (guard : NLF_RefCell.Guard) (lane : Bytes) (page first : UInt64)
      (roots : List Digest) : Call Unit
  | appendRoots (guard : NLF_RefCell.Guard) (header : Header) (roots : List Digest) : Call Unit
/-- Logs retain full typed call arguments, full reply, and complete snapshots.
Child events are inserted between enter and leave, including internal loans
and system CPIs. No event after an abort is manufactured. -/
inductive PCA_Event where
  | enter {α : Type} (site : Nat) (call : Call α) (before : PCA_State)
  | leave {α : Type} (site : Nat) (reply : Outcome α) (after : PCA_State)
  | branch (site : Nat) (taken : Bool)
  | mapError (site : Nat) (fromCode toCode : ProgramError)
  | propagate (site : Nat) (code : ProgramError)
  | token (event : NLF_ParentModel.Event)
  | copy (site : Nat) (guard : NLF_RefCell.Guard) (bytes : Bytes)
  | cpiBegin (invocation : Invocation)
  | cpiReply (reply : Outcome Unit)
  | syscall (name : String) (arguments : List Bytes) (reply : Outcome Bytes)
  | aborted (reason : String)
  | returned (reply : Outcome Unit)
structure Execution (α : Type) where
  state : PCA_State
  events : List PCA_Event
  reply : Outcome α
/-- Intermediate oracle interface only. It is never a row root hypothesis.
Every implementation needs a typed child packet and SAME-argument discharge. -/
abbrev Children := {α : Type} → Nat → Call α → PCA_State → Execution α
end PCA
