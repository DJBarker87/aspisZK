-- PCWF item C (NGD_SlotRef): fresh 4bb3b3f emission PCWF_E001 (aspis-r1-cost-probe compact.rs, overflow-checks OFF, root crate::compact::slot_offset)
-- against the gate NGD_SlotRef.Funs. Gate constant OFF_NODES : Usize := 28359 is a literal; the frozen constant is the Result chain below.
import Aeneas
import NGD_SlotRef.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace NGD_SlotRef
namespace PRVFresh_NGD_SlotRef
/-- [aspis_r1_cost_probe::compact::HEADER]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 26:0-26:29
    Visibility: public -/
@[global_simps, irreducible] def compact.HEADER : Std.Usize := 16#usize

/-- [aspis_r1_cost_probe::compact::QUERIES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 28:0-28:30
    Visibility: public -/
@[global_simps, irreducible] def compact.QUERIES : Std.Usize := 22#usize

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

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::compact::COMPACT_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 35:0-35:38
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

/-- [aspis_r1_cost_probe::compact::OPENING]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 37:0-37:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OPENING : Result Std.Usize := do
  let i ← 480#usize + 128#usize
  let i1 ← i + 32#usize
  let i2 ← i1 + 32#usize
  let i3 ← i2 + 128#usize
  i3 + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 38:0-38:39
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

/-- [aspis_r1_cost_probe::compact::OFF_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 39:0-39:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

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

/-- [aspis_r1_cost_probe::compact::OFF_FINAL]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 44:0-44:46
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FINAL : Result Std.Usize := do
  let i ← compact.OFF_ROUND1
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::FINAL_LEN]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 45:0-45:32
    Visibility: public -/
@[global_simps, irreducible] def compact.FINAL_LEN : Std.Usize := 64#usize

/-- [aspis_r1_cost_probe::compact::OFF_OPENINGS]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 46:0-46:59
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_OPENINGS : Result Std.Usize := do
  let i ← compact.FINAL_LEN * 32#usize
  let i1 ← compact.OFF_FINAL
  i1 + i

/-- [aspis_r1_cost_probe::compact::OFF_NODES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 47:0-47:62
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_NODES : Result Std.Usize := do
  let i ← compact.OPENING
  let i1 ← compact.QUERIES * i
  let i2 ← compact.OFF_OPENINGS
  i2 + i1

/-- [aspis_r1_cost_probe::compact::SLOT_NODES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 54:0-54:66
    Visibility: public -/
@[global_simps, irreducible]
def compact.SLOT_NODES : Array Std.Usize 6#usize :=
  Array.make 6#usize [
    146#usize, 146#usize, 128#usize, 172#usize, 172#usize, 150#usize
    ]

/-- [aspis_r1_cost_probe::compact::slot_offset]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 59:4-62:5
    Visibility: public -/
def compact.slot_offset_loop.body
  (slot : Std.Usize) (at1 : Std.Usize) (i : Std.Usize) :
  Result (ControlFlow (Std.Usize × Std.Usize) Std.Usize)
  := do
  if i < slot
  then
    let i1 ← Array.index_usize compact.SLOT_NODES i
    let i2 ← lift (Std.Usize.wrapping_mul 32#usize i1)
    let at2 ← lift (Std.Usize.wrapping_add at1 i2)
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (at2, i3))
  else ok (done at1)

/-- [aspis_r1_cost_probe::compact::slot_offset]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 59:4-62:5
    Visibility: public -/
def compact.slot_offset_loop
  (slot : Std.Usize) (at1 : Std.Usize) (i : Std.Usize) : Result Std.Usize := do
  loop
    (fun (at2, i1) => compact.slot_offset_loop.body slot at2 i1)
    (at1, i)

/-- [aspis_r1_cost_probe::compact::slot_offset]:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 56:0-64:1
    Visibility: public -/
def compact.slot_offset (slot : Std.Usize) : Result Std.Usize := do
  let at1 ← compact.OFF_NODES
  compact.slot_offset_loop slot at1 0#usize

end PRVFresh_NGD_SlotRef
end NGD_SlotRef

theorem lit_add (a b c : Std.Usize) (h : a.val + b.val = c.val) : (a + b : Result Std.Usize) = ok c := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem lit_mul (a b c : Std.Usize) (h : a.val * b.val = c.val) : (a * b : Result Std.Usize) = ok c := by
  have hmax : a.val * b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.mul_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem lit_sub (a b c : Std.Usize) (h : a.val - b.val = c.val) (hle : b.val ≤ a.val) : (a - b : Result Std.Usize) = ok c := by
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.sub_spec (x := a) (y := b) hle)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem c_HEADER : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.HEADER = 16#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.HEADER; rfl
theorem c_QUERIES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.QUERIES = 22#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.QUERIES; rfl
theorem c_FINAL_LEN : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.FINAL_LEN = 64#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.FINAL_LEN; rfl
theorem c_OFF_SEMANTIC : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_SEMANTIC = 16#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_SEMANTIC; exact c_HEADER

theorem v_verifier_SEMANTIC_BYTES : NGD_SlotRef.PRVFresh_NGD_SlotRef.verifier.SEMANTIC_BYTES = ok 13831#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.verifier.SEMANTIC_BYTES
  have h0 : (29#usize * 32#usize : Result Std.Usize) = ok 928#usize := lit_mul _ _ _ (by scalar_tac)
  have h1 : (12903#usize + 928#usize : Result Std.Usize) = ok 13831#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, h1, bind_tc_ok]

theorem v_compact_LOGICAL_SEMANTIC : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.LOGICAL_SEMANTIC = ok 13831#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.LOGICAL_SEMANTIC
  simp only [v_verifier_SEMANTIC_BYTES, bind_tc_ok]

theorem v_compact_SEMANTIC_COMPACT_VALUES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.SEMANTIC_COMPACT_VALUES
  have h0 : (10#usize * 28#usize : Result Std.Usize) = ok 280#usize := lit_mul _ _ _ (by scalar_tac)
  have h1 : (1#usize + 280#usize : Result Std.Usize) = ok 281#usize := lit_add _ _ _ (by scalar_tac)
  have h2 : (87#usize + 29#usize : Result Std.Usize) = ok 116#usize := lit_add _ _ _ (by scalar_tac)
  have h3 : (281#usize + 116#usize : Result Std.Usize) = ok 397#usize := lit_add _ _ _ (by scalar_tac)
  have h4 : (397#usize + 29#usize : Result Std.Usize) = ok 426#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, h1, h2, h3, h4, bind_tc_ok]

theorem v_compact_COMPACT_SEMANTIC : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.COMPACT_SEMANTIC = ok 7015#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.COMPACT_SEMANTIC
  have h0 : (16#usize * 426#usize : Result Std.Usize) = ok 6816#usize := lit_mul _ _ _ (by scalar_tac)
  have h1 : (13831#usize - 6816#usize : Result Std.Usize) = ok 7015#usize := lit_sub _ _ _ (by scalar_tac) (by scalar_tac)
  simp only [h0, h1, v_compact_SEMANTIC_COMPACT_VALUES, v_compact_LOGICAL_SEMANTIC, bind_tc_ok]

theorem v_compact_COMPACT_Y1 : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.COMPACT_Y1 = ok 464#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.COMPACT_Y1
  have h0 : (29#usize * 16#usize : Result Std.Usize) = ok 464#usize := lit_mul _ _ _ (by scalar_tac)
  simp only [h0, bind_tc_ok]

theorem v_compact_OPENING : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OPENING = ok 832#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OPENING
  have h0 : (480#usize + 128#usize : Result Std.Usize) = ok 608#usize := lit_add _ _ _ (by scalar_tac)
  have h1 : (608#usize + 32#usize : Result Std.Usize) = ok 640#usize := lit_add _ _ _ (by scalar_tac)
  have h2 : (640#usize + 32#usize : Result Std.Usize) = ok 672#usize := lit_add _ _ _ (by scalar_tac)
  have h3 : (672#usize + 128#usize : Result Std.Usize) = ok 800#usize := lit_add _ _ _ (by scalar_tac)
  have h4 : (800#usize + 32#usize : Result Std.Usize) = ok 832#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, h1, h2, h3, h4, bind_tc_ok]

theorem v_compact_OFF_Y1 : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_Y1 = ok 7031#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_Y1
  have h0 : (16#usize + 7015#usize : Result Std.Usize) = ok 7031#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_COMPACT_SEMANTIC, c_OFF_SEMANTIC, bind_tc_ok]

theorem v_compact_OFF_INACTIVE : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_INACTIVE = ok 7495#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_INACTIVE
  have h0 : (7031#usize + 464#usize : Result Std.Usize) = ok 7495#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_OFF_Y1, v_compact_COMPACT_Y1, bind_tc_ok]

theorem v_compact_OFF_ROUND0 : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_ROUND0 = ok 7527#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_ROUND0
  have h0 : (7495#usize + 32#usize : Result Std.Usize) = ok 7527#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_OFF_INACTIVE, bind_tc_ok]

theorem v_compact_OFF_FOLDED_ROOT : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_FOLDED_ROOT = ok 7751#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_FOLDED_ROOT
  have h0 : (7527#usize + 224#usize : Result Std.Usize) = ok 7751#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_OFF_ROUND0, bind_tc_ok]

theorem v_compact_OFF_ROUND1 : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_ROUND1 = ok 7783#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_ROUND1
  have h0 : (7751#usize + 32#usize : Result Std.Usize) = ok 7783#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_OFF_FOLDED_ROOT, bind_tc_ok]

theorem v_compact_OFF_FINAL : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_FINAL = ok 8007#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_FINAL
  have h0 : (7783#usize + 224#usize : Result Std.Usize) = ok 8007#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, v_compact_OFF_ROUND1, bind_tc_ok]

theorem v_compact_OFF_OPENINGS : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_OPENINGS = ok 10055#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_OPENINGS
  have h0 : (64#usize * 32#usize : Result Std.Usize) = ok 2048#usize := lit_mul _ _ _ (by scalar_tac)
  have h1 : (8007#usize + 2048#usize : Result Std.Usize) = ok 10055#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, h1, v_compact_OFF_FINAL, c_FINAL_LEN, bind_tc_ok]

theorem v_compact_OFF_NODES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_NODES = ok 28359#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_NODES
  have h0 : (22#usize * 832#usize : Result Std.Usize) = ok 18304#usize := lit_mul _ _ _ (by scalar_tac)
  have h1 : (10055#usize + 18304#usize : Result Std.Usize) = ok 28359#usize := lit_add _ _ _ (by scalar_tac)
  simp only [h0, h1, v_compact_OPENING, v_compact_OFF_OPENINGS, c_QUERIES, bind_tc_ok]

theorem PRVEq.NGD_SlotRef.Funs.OFF_NODES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_NODES = ok NGD_SlotRef.OFF_NODES := by
  rw [v_compact_OFF_NODES]; delta NGD_SlotRef.OFF_NODES; rfl
#print axioms PRVEq.NGD_SlotRef.Funs.OFF_NODES

theorem PRVEq.NGD_SlotRef.Funs.SLOT_NODES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.SLOT_NODES = NGD_SlotRef.SLOT_NODES := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.SLOT_NODES NGD_SlotRef.SLOT_NODES; rfl
#print axioms PRVEq.NGD_SlotRef.Funs.SLOT_NODES

theorem PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body : @NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset_loop.body = @NGD_SlotRef.slot_offset_loop.body := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset_loop.body NGD_SlotRef.slot_offset_loop.body
  simp only [PRVEq.NGD_SlotRef.Funs.SLOT_NODES]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body

theorem PRVEq.NGD_SlotRef.Funs.slot_offset_loop : @NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset_loop = @NGD_SlotRef.slot_offset_loop := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset_loop NGD_SlotRef.slot_offset_loop
  simp only [PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset_loop

theorem PRVEq.NGD_SlotRef.Funs.slot_offset : @NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset = @NGD_SlotRef.slot_offset := by
  funext slot
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.slot_offset NGD_SlotRef.slot_offset
  simp only [PRVEq.NGD_SlotRef.Funs.OFF_NODES, bind_tc_ok, PRVEq.NGD_SlotRef.Funs.slot_offset_loop]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset
