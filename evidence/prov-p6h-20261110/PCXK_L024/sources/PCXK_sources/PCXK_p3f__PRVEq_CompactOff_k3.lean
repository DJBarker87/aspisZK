-- PCVF_ compact.OFF_* (CurrentCompactCallerModelV1: OFF_SEMANTIC, OFF_Y1, OFF_INACTIVE, OFF_FOLDED_ROOT, OFF_ROUND1).
-- Fresh text: PCQF_E006 emission (prov-p1e-20261109, overflow ON, frozen 4bb3b3f), compact constants chain FINAL_LEN..OFF_ROUND1.
-- The gate constants are functions of an `Ops` record whose slots op12, op13, op14, op21 stand for the constants HEADER-based OFF_SEMANTIC,
-- COMPACT_SEMANTIC, COMPACT_Y1 and OFF_ROUND0. The statements are fresh = gate under that binding (Bound); the gate has no OFF_ROUND0 constant (op21).
-- RESULT CLASS: CONDITIONAL_ON_BINDING (the deployed Ops must be shown to carry these four constants; the Ops instance constructed here
-- from the fresh constants shows the binding is satisfiable).
import Aeneas
import CurrentCompactCallerModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1CurrentCaller
namespace PRVFresh_k3

@[global_simps, irreducible] def compact.FINAL_LEN : Std.Usize := 64#usize

/-- [aspis_r1_cost_probe::compact::HEADER]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 26:0-26:29
    Visibility: public -/
@[global_simps, irreducible] def compact.HEADER : Std.Usize := 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 38:0-38:39
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

/-- [aspis_r1_cost_probe::compact::SEMANTIC_COMPACT_VALUES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 33:0-33:72
    Visibility: public -/
@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

/-- [aspis_r1_cost_probe::verifier::SEMANTIC_BYTES]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 8:0-8:43
    Visibility: public -/
@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

/-- [aspis_r1_cost_probe::compact::LOGICAL_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 31:0-31:68
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::compact::OFF_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 39:0-39:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

/-- [aspis_r1_cost_probe::compact::COMPACT_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 35:0-35:38
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_INACTIVE]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 40:0-40:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_INACTIVE : Result Std.Usize := do
  let i ← compact.OFF_Y1
  let i1 ← compact.COMPACT_Y1
  i + i1

/-- [aspis_r1_cost_probe::compact::OFF_ROUND0]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 41:0-41:48
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND0 : Result Std.Usize := do
  let i ← compact.OFF_INACTIVE
  i + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_FOLDED_ROOT]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 42:0-42:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FOLDED_ROOT : Result Std.Usize := do
  let i ← compact.OFF_ROUND0
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::OFF_ROUND1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 43:0-43:51
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND1 : Result Std.Usize := do
  let i ← compact.OFF_FOLDED_ROOT
  i + 32#usize


end PRVFresh_k3
end AspisR1CurrentCaller

namespace PRVEq.CompactOff_k3
open AspisR1CurrentCaller

structure Bound (ops : Ops) : Prop where
  h12 : ops.op12 = ok PRVFresh_k3.compact.OFF_SEMANTIC
  h13 : ops.op13 = PRVFresh_k3.compact.COMPACT_SEMANTIC
  h14 : ops.op14 = PRVFresh_k3.compact.COMPACT_Y1
  h21 : ops.op21 = PRVFresh_k3.compact.OFF_ROUND0

set_option maxHeartbeats 200000
theorem OFF_SEMANTIC_eq (ops : Ops) (b : Bound ops) :
    (ok PRVFresh_k3.compact.OFF_SEMANTIC : Result Std.Usize) = compact.OFF_SEMANTIC ops := by
  unfold compact.OFF_SEMANTIC; rw [b.h12]

theorem OFF_Y1_eq (ops : Ops) (b : Bound ops) :
    PRVFresh_k3.compact.OFF_Y1 = compact.OFF_Y1 ops := by
  unfold PRVFresh_k3.compact.OFF_Y1 compact.OFF_Y1
  rw [← OFF_SEMANTIC_eq ops b, b.h13]; rfl

theorem OFF_INACTIVE_eq (ops : Ops) (b : Bound ops) :
    PRVFresh_k3.compact.OFF_INACTIVE = compact.OFF_INACTIVE ops := by
  unfold PRVFresh_k3.compact.OFF_INACTIVE compact.OFF_INACTIVE
  rw [← OFF_Y1_eq ops b, b.h14]

theorem OFF_FOLDED_ROOT_eq (ops : Ops) (b : Bound ops) :
    PRVFresh_k3.compact.OFF_FOLDED_ROOT = compact.OFF_FOLDED_ROOT ops := by
  unfold PRVFresh_k3.compact.OFF_FOLDED_ROOT compact.OFF_FOLDED_ROOT
  rw [b.h21]

theorem OFF_ROUND1_eq (ops : Ops) (b : Bound ops) :
    PRVFresh_k3.compact.OFF_ROUND1 = compact.OFF_ROUND1 ops := by
  unfold PRVFresh_k3.compact.OFF_ROUND1 compact.OFF_ROUND1
  rw [OFF_FOLDED_ROOT_eq ops b]

end PRVEq.CompactOff_k3
set_option maxHeartbeats 200000
#print axioms PRVEq.CompactOff_k3.OFF_SEMANTIC_eq
#print axioms PRVEq.CompactOff_k3.OFF_Y1_eq
#print axioms PRVEq.CompactOff_k3.OFF_INACTIVE_eq
#print axioms PRVEq.CompactOff_k3.OFF_FOLDED_ROOT_eq
#print axioms PRVEq.CompactOff_k3.OFF_ROUND1_eq
