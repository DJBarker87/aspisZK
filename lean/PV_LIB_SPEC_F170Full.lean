import PV_LIB_SPEC_F6Full
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F170Full
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- The row's OWN entry, all source arguments and valid registered references,
OWNER/header invariants and numbering. No callback success, write-definedness,
replacement Effects dictionary, pending-world frame or future read. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F170.live 2 r i
/-- Post_thread_f170: Select the source initializer token, consume its arbitrary reply, and invoke the actual callback on the returned TLS reference; return the Result and retain every failure or missing-representation branch.

Both getter and setter contexts must be covered by the same row. Source TLS initializer468/469, Option as_ref277/ok_or278, Result branch279/from_residual280 and callback dispatch use provider constructors by name. Pure leaves preserve world on every answer (thread24). The setter executes f207 and the f289 concrete source-cell write; no arbitrary Effects field or write-definedness premise is admitted in MachineSpec.
Use source-encoded Option/Result/ControlFlow values, not a world-dependent
opaque marker. All responses remain in the domain. The final table parameter
includes source writes289 and any boxed Cell/atomic state found under D984. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F170.live i candidate
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)
/-- A paired comparison, not a cross-cohort import or implication proof.
packageContract is the literal typed PackageContract of F170PackageComparison
in the original W4 cohort. It is NOT a premise of the new Contract. -/
def Comparison (packageContract : Prop) (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageContract ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end PV_LIB_SPEC_F170Full
