-- PCWT_ binding discharge for the CurrentCompactCallerModelV1 constant keys: compact.OFF_SEMANTIC, OFF_Y1, OFF_INACTIVE, OFF_FOLDED_ROOT, OFF_ROUND1, LOGICAL_SEMANTIC. Route (b).
-- What was bound (PCVF_ k3, PCVK_ k3): the gate constants are functions of the Ops record; slots op12 (HEADER-based OFF_SEMANTIC), op13 (COMPACT_SEMANTIC), op14 (COMPACT_Y1),
-- op15 (LOGICAL_SEMANTIC), op21 (OFF_ROUND0) stand for constants of crates/aspis-r1-cost-probe/src/compact.rs (26:0, 31:0, 34:0, 35:0, 41:0), fresh text PCQF_E006 (frozen 4bb3b3f, ON).
-- Here ops1 ops0 is ANY base Ops with exactly these five slots set to the fresh frozen constants; the statements hold for every ops0, including the installed dictionary.
-- Not claimed: that a particular deployed dictionary already carries these slot values (the installers of RPz7_Uni_Install etc. were not searched for them).
import Aeneas
import CurrentCompactCallerModelV1
import PRVEq_CompactOff_k3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

namespace PRVEq.CompactOff_t7
open AspisR1CurrentCaller

def ops1 (ops0 : Ops) : Ops :=
  { ops0 with
    op12 := ok PRVFresh_k3.compact.OFF_SEMANTIC
    op13 := PRVFresh_k3.compact.COMPACT_SEMANTIC
    op14 := PRVFresh_k3.compact.COMPACT_Y1
    op15 := PRVFresh_k3.compact.LOGICAL_SEMANTIC
    op21 := PRVFresh_k3.compact.OFF_ROUND0 }

theorem bound (ops0 : Ops) : PRVEq.CompactOff_k3.Bound (ops1 ops0) := ⟨rfl, rfl, rfl, rfl⟩

theorem OFF_SEMANTIC_frozen (ops0 : Ops) :
    (ok PRVFresh_k3.compact.OFF_SEMANTIC : Result Std.Usize) = compact.OFF_SEMANTIC (ops1 ops0) :=
  PRVEq.CompactOff_k3.OFF_SEMANTIC_eq _ (bound ops0)

theorem OFF_Y1_frozen (ops0 : Ops) : PRVFresh_k3.compact.OFF_Y1 = compact.OFF_Y1 (ops1 ops0) :=
  PRVEq.CompactOff_k3.OFF_Y1_eq _ (bound ops0)

theorem OFF_INACTIVE_frozen (ops0 : Ops) : PRVFresh_k3.compact.OFF_INACTIVE = compact.OFF_INACTIVE (ops1 ops0) :=
  PRVEq.CompactOff_k3.OFF_INACTIVE_eq _ (bound ops0)

theorem OFF_FOLDED_ROOT_frozen (ops0 : Ops) : PRVFresh_k3.compact.OFF_FOLDED_ROOT = compact.OFF_FOLDED_ROOT (ops1 ops0) :=
  PRVEq.CompactOff_k3.OFF_FOLDED_ROOT_eq _ (bound ops0)

theorem OFF_ROUND1_frozen (ops0 : Ops) : PRVFresh_k3.compact.OFF_ROUND1 = compact.OFF_ROUND1 (ops1 ops0) :=
  PRVEq.CompactOff_k3.OFF_ROUND1_eq _ (bound ops0)

theorem LOGICAL_SEMANTIC_frozen (ops0 : Ops) : PRVFresh_k3.compact.LOGICAL_SEMANTIC = compact.LOGICAL_SEMANTIC (ops1 ops0) := by
  unfold compact.LOGICAL_SEMANTIC
  rfl

end PRVEq.CompactOff_t7
#print axioms PRVEq.CompactOff_t7.OFF_SEMANTIC_frozen
#print axioms PRVEq.CompactOff_t7.OFF_Y1_frozen
#print axioms PRVEq.CompactOff_t7.OFF_INACTIVE_frozen
#print axioms PRVEq.CompactOff_t7.OFF_FOLDED_ROOT_frozen
#print axioms PRVEq.CompactOff_t7.OFF_ROUND1_frozen
#print axioms PRVEq.CompactOff_t7.LOGICAL_SEMANTIC_frozen
