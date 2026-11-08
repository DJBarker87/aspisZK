import PV_LIB_SPEC_F6Full
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F5Full
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- The row's OWN entry, all source arguments and valid registered references,
OWNER/header invariants and numbering. No callback success, write-definedness,
replacement Effects dictionary, pending-world frame or future read. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F5.live 0 r i
/-- Post_thread_f5: Set the active worker flag through the actual callback and return the guard, retaining TLS failure and its declared write.

The callback uses CLOSED207/CLOSED289 with actual Cell reference and replacement true. Return the source guard and retain the concrete Cell write, even though the callback return value alone does not expose it.
Use source-encoded Option/Result/ControlFlow values, not a world-dependent
opaque marker. All responses remain in the domain. The final table parameter
includes source writes289 and any boxed Cell/atomic state found under D984. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F5.live i candidate
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)
/-- A paired comparison, not a cross-cohort import or implication proof.
packageContract is the literal typed PackageContract of F5PackageComparison
in the original W4 cohort. It is NOT a premise of the new Contract. -/
def Comparison (packageContract : Prop) (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageContract ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end PV_LIB_SPEC_F5Full
