import PV_LIB_SPEC_F361Full
import PV_FN_THREAD_f166SummaryRun
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F166Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F166.live 2 r i
/-- Post_thread_f166: Construct Builder, invoke spawn_scoped and consume its Result; on success return ScopedJoinHandle with the actual captures, preserving exact OS/failure effects.

Builder fields are source literals. f270 receives actual scope and moved closure. On Ok return its scoped handle; on Err the source expect child takes its panic/abort path including any formatting allocation before diagnostic effects.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F166.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_FN_THREAD_f166SummaryRun
/-- Exact proposition of the package's PV_FN_THREAD_f166SummaryRun.from_entry,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 c8a587950ff3c91d53a61bca5aee01c3e023af88dae84f539960f6204d5649fe. -/
def PackageStatement : Prop := ∀ {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config),
  PV_THR2_IntrinsicState.advance B K programs H
      (steps B H (entry s a parents w es stack)) (entry s a parents w es stack) =
      after B H (entry s a parents w es stack)
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
end PV_LIB_SPEC_F166Full
