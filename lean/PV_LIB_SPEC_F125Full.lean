import PV_LIB_SPEC_F361Full
import PV_THR2_Catch125Prefix
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F125Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F125.live 1 r i
/-- Post_thread_f125: Return catch_unwind Result after running std::panicking::catch_unwind on those arguments; preserve the exact callback effects and pinned panic strategy.

Invoke f219 at the actual callback/capture arguments; transport the nested Result exactly. Under client panic=abort do not manufacture a caught-unwind success.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F125.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_THR2_Catch125Prefix
/-- Exact proposition of the package's PV_THR2_Catch125Prefix.run,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 c071373b12ec70c81836eafc1cb6d3927fbf0a99d9167c62b3750f7c04d7a55a. -/
def PackageStatement : Prop := ∀ {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (capture : Data) (w : W) (es : List E)
    (cell : s.cells ⟨a,1,[]⟩ = some capture),
  PV_THR2_Execution.advance base ctl
      (PV_THR2_ScopeChildren.table (PV_THR2_ScopeWrappers.resolve programs)) handler 5
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F125.live.body},parents,s⟩,w,es⟩ =
    ⟨.running (entered s a parents capture),w,es⟩
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
end PV_LIB_SPEC_F125Full
