import PV_LIB_SPEC_F166Whole
import PV_THR2_Catch208Invoke
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F208Whole
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Row.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F208.live 2 r i
/-- Post_thread_f208: Invoke the user closure f15 with the actual scope reference and captures and return its value/effects.

Unpack the source scope closure captures, pass the actual scope reference to f15, and propagate every result, store and effect without taking a second callback reply.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadRow.Post table r PV_THR2_F208.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_THR2_Catch208Invoke
/-- Exact proposition of the package's PV_THR2_Catch208Invoke.issue,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 445bd84e19ad9f13af0b2409266e28c2a8990d82cc95a329acc23165e3dfcb54. -/
def PackageStatement : Prop := ∀ {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (payload : Data) (p : Address) (w : W)
    (cell3 : s.cells ⟨a,3,[]⟩ = some payload)
    (cell4 : s.cells ⟨a,4,[]⟩ = some (PV_THR2_KeyValues.pack PV_THR2_Catch208References.tupleKind
      [PV_STX2_TypedReferences.reference p .null])),
  PV_THR2_Execution.step base ctl programs handler
      ⟨{activation := a,remaining := PV_THR2_F208.live.body.drop 11},parents,s⟩ w =
      ⟨.running (pending s a parents payload p),w,[]⟩
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
end PV_LIB_SPEC_F208Whole
