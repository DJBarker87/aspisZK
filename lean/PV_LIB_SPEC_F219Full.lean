import PV_LIB_SPEC_F361Full
import PV_THR2_Catch219Prologue
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F219Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F219.live 1 r i
/-- Post_thread_f219: Invoke the preserved higher-order intrinsic once at its actual arguments and retain the callback result/explicit final store; preserve abort under pinned panic strategy.

The preserved intrinsic318 runs do_call316 ONCE with actual data; ManuallyDrop/new/take/into_inner use emitted representations. The callback result is stored in its argument-reachable result cell. Full Result arms and panic=abort are retained.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F219.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_THR2_Catch219Prologue
/-- Exact proposition of the package's PV_THR2_Catch219Prologue.run,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 9f3ebaa1a84d589c3279acafa7db18fbfcdfc7ec0475f60c182f5bea87fad96c. -/
def PackageStatement : Prop := ∀ {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (capture : Data) (w : W) (es : List E)
    (cell : s.cells ⟨a,1,[]⟩ = some capture),
  PV_THR2_Execution.advance base ctl programs handler 5
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body},parents,s⟩,w,es⟩ =
    ⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 5},parents,afterStore s a capture⟩,w,es⟩
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
end PV_LIB_SPEC_F219Full
