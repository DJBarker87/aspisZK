import PV_LIB_SPEC_F361Full
import PV_FN_THREAD_f270SummaryRun
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F270Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F270.live 3 r i ∧ ∃ builder scope closure, i.arguments = [builder,scope,closure] ∧
    PV_THR2_TypedRepresentation_Builder.Shape builder ∧
    ∃ threadLabel size hooks, r.carrier.field builder 0 = some threadLabel ∧
      r.carrier.field builder 1 = some size ∧ r.carrier.field builder 2 = some hooks
/-- Post_thread_f270: Clone scope bookkeeping and invoke spawn_unchecked with the actual closure and scope; return the actual scoped handle/Result with exact OS resource branches.

Use Builder.name and stack_size, clone the actual Scope Arc with nonzero strong count derived from construction, and pass the moved worker closure to f361. On source Err retain the exact error and earlier callback/Thread/Box allocations, not a post-success-only allocation arm.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F270.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_FN_THREAD_f270SummaryRun
/-- Exact proposition of the package's PV_FN_THREAD_f270SummaryRun.from_entry,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 0630ba98d92614ce4a91aeeba8b702b3171272503a2e35a9537b769d6eb61cd2. -/
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
end PV_LIB_SPEC_F270Full
