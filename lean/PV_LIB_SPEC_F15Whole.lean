import PV_LIB_SPEC_F166Whole
import PV_THR2_Source15Prologue
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F15Whole
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Row.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F15.live 2 r i
/-- Post_thread_f15: Construct handles, iterate next93, spawn f166 on each Some index with source-derived captures, push handles and join in source order; None exits without a ThreadInit allocation, preserving failures and explicit stores.

On next93 Some i execute exactly the source spawn of i with actual n/f/scope capture and then push its handle; None exits without allocating a ThreadInit for that iteration. Joins and result order are preserved. The range start and handle Vec header writes are actual source-store actions, not backend-only changes.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadRow.Post table r PV_THR2_F15.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_THR2_Source15Prologue
/-- Exact proposition of the package's PV_THR2_Source15Prologue.run,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 def752723cdef93135586c9e1c3c8158b3004167f8c647788d960a71d721ef20. -/
def PackageStatement : Prop := ∀ {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (p : Address)
    (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,2,[]⟩ = some (PV_THR2_KeyValues.pack PV_THR2_Catch208References.tupleKind
      [PV_STX2_TypedReferences.reference p .null])),
  PV_THR2_IntrinsicState.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b) ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 4},parents,afterStore s a p⟩,w,es⟩,stack⟩
/-- Explicit side-by-side obligations. No implication, equivalence or proof
of the new whole contract is inferred from the package's prefix theorem. -/
def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PackageStatement ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F15Whole
