import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA
/-- Descriptors to be PRODUCED by native cuts, not fabricated typed SDK guards.
Cell identities stand for related RefCell allocations, not address tests. -/
structure NativeAccountView where
  key : Bytes
  owner : Bytes
  dataCell : Nat
  lamportsCell : Nat
  data : Bytes
  lamports : Nat
  signer : Bool
  writable : Bool
  executable : Bool
  rentEpoch : Nat
structure NativeInputView where
  program : Key
  instruction : Bytes
  rent : Rent
  accounts : List NativeAccountView

/-- PCC-NativeView: SAME current views and RefCell identities. This is an
OPEN source-association obligation, never an accepted native row premise. -/
def NativeView (native : NativeInputView) (model : PCA_State) : Prop :=
  native.program = model.programId ∧ native.instruction = model.instructionData ∧
  native.rent = model.rent ∧ native.accounts.length = model.accountCount ∧
  ∀ i (hi : i < native.accounts.length),
    let n := native.accounts[i]
    let a := model.loans.state.accounts i
    n.key = a.key ∧ n.owner = a.owner ∧ n.dataCell = a.data ∧ n.lamportsCell = a.lamports ∧
    n.data = (model.loans.state.cells a.data).payload.bytes ∧
    n.lamports = (model.loans.state.cells a.lamports).payload.money ∧
    n.signer = a.signer ∧ n.writable = a.writable ∧ n.executable = a.executable ∧
    n.rentEpoch = a.rentEpoch

/-- PCC-MachineWord: bounds on native usize/u64 input fields only.
Borrow-counter linkage is a separate current-state SDK obligation. -/
def MachineWord (native : NativeInputView) : Prop :=
  native.accounts.length < 2^64 ∧ native.instruction.length < 2^64 ∧
  ∀ a ∈ native.accounts, a.data.length < 2^64 ∧ a.lamports < 2^64 ∧ a.rentEpoch < 2^64

/-- PCC-InitialState: initial model setup, not an admission at later cuts. -/
def InitialState (model : PCA_State) : Prop :=
  Invariant model ∧ model.liveGuards = [] ∧ model.loans.events = [] ∧
  model.cpiHistory = [] ∧ model.syscallHistory = [] ∧ model.returned = none
end PCC
