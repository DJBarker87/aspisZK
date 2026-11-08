import PV_LIB_SPEC_F270Whole
import PV_FN_THREAD_f166SummaryRun
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_ThreadRow
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
/-- Prefix framing retains the original suspended stack as a suffix: the
intrinsic temporarily pushes its own saved frames. Equality is appropriate
only after those frames are restored, never at a pending callback prefix. -/
def Frame (r : Runtime) (i : Input) (q : State) : Prop :=
  let s := PV_W1_LeafBoundary.statusStore q.current.status
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world s.nextActivation ∧
  Numbered q ∧ (∃ own, q.suspended = own ++ i.suspended) ∧
  (∃ suffix, q.current.events = i.events ++ suffix) ∧
  ∀ p : Address, p.activation < i.activation →
    p ≠ ⟨i.parent.activation,i.destination,[]⟩ →
    ¬ PV_W1_ArgumentEffects.Writable r.carrier (leafEntry i) i.world p →
      s.cells p = i.store.cells p

/-- Whole source-order behavior and prefix framing, including nested callback
pending and every failure/abort. No unchanged heap/backend assertion is used:
Behavior compares their EXACT actual model effects. -/
def Post (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (i : Input) (candidate : Nat → State) : Prop :=
  Behavior (source table r) (entry body i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ Boundary (source table r) (entry body i) candidate j) →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => Frame r i (candidate k)

/-- Literal comparison with the earlier no-intrinsic-prefix frame. No claim
that equality holds while the intrinsic has a saved parent on its stack. -/
def FrameComparison (r : Runtime) (i : Input) (q : State) : Prop :=
  (PV_LIB_SPEC_Row.Frame r i q → Frame r i q) ∧
  (q.suspended = i.suspended → (Frame r i q ↔ PV_LIB_SPEC_Row.Frame r i q))

#print axioms Frame
#print axioms Post
#print axioms FrameComparison
end PV_LIB_SPEC_ThreadRow

namespace PV_LIB_SPEC_F166Whole
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Row.MachineSpec

def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F166.live 2 r i

/-- Actual Scope::spawn: construct Builder with source literals, move the
closure into270, consume the whole Result through expect271, return the real
handle or the exact panic/resource frontier. Formatting allocation is inside
the source child model, before its diagnostic event. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadRow.Post table r PV_THR2_F166.live i candidate

def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

/-- Exact retained caller-only package statement (not a callee contract). -/
def PackageStatement (r : Runtime) (i : Input) : Prop :=
  PV_THR2_IntrinsicState.advance r.carrier r.control PV_FN_THREAD_f166SummaryRun.programs
    r.native (PV_FN_THREAD_f166SummaryRun.steps r.carrier r.native
      (entry PV_THR2_F166.live i)) (entry PV_THR2_F166.live i) =
    PV_FN_THREAD_f166SummaryRun.after r.carrier r.native (entry PV_THR2_F166.live i)

def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ i, PackageStatement r i) ∧ Contract table r implementation

#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F166Whole
