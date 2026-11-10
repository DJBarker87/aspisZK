-- PCVU_ item (1): QM31::from_le_bytes (frozen 4bb3b3f emission PCVU_E001, overflow ON) against the deployed decode_k_spec + fromK.
-- Fresh emission text wrapped in namespace PCVU_Fresh with the Types replaced by the gate abbrevs (AspisR1Stage2.aspis_core.field.*).
-- Holds on 16-byte windows only; decode_k_spec has no length check (see the note below the theorem).
import Aeneas
import PRVEq_E32_s4
import PRVEq_Tx2Deployed_s1
import CheckpointBytes3KDecode
import CheckpointBytes3Word
import CheckpointBytes3ScalarShape
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
noncomputable section
namespace PCVU_QM31
attribute [local instance] Classical.propDecidable
namespace PCVU_Fresh
abbrev field.M31 := AspisR1Stage2.aspis_core.field.M31
abbrev field.CM31 := AspisR1Stage2.aspis_core.field.CM31
abbrev field.QM31 := AspisR1Stage2.aspis_core.field.QM31
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::M31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/field.rs', lines 239:4-246:5
    Visibility: public -/
def field.M31.from_le_bytes
  (bytes : Array Std.U8 4#usize) : Result (Option field.M31) := do
  let v ← lift (core.num.U32.from_le_bytes bytes)
  if v >= field.P
  then ok none
  else ok (some v)

/-- [aspis_core::field::{aspis_core::field::CM31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/field.rs', lines 410:4-422:5
    Visibility: public -/
def field.CM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.CM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 4#usize }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  match r with
  | core.result.Result.Ok value =>
    let o ← field.M31.from_le_bytes value
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := 4#usize, «end» := 8#usize }
      let r1 ←
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s1
      match r1 with
      | core.result.Result.Ok value1 =>
        let o1 ← field.M31.from_le_bytes value1
        let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          ok (some { a := val, b := val1 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
            field.CM31 residual
      | core.result.Result.Err _ => ok none
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        field.CM31 residual
  | core.result.Result.Err _ => ok none

/-- [aspis_core::field::{aspis_core::field::QM31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/field.rs', lines 1022:4-1026:5
    Visibility: public -/
def field.QM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.QM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 8#usize }
  let o ← field.CM31.from_le_bytes s
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := 8#usize, «end» := 16#usize }
    let o1 ← field.CM31.from_le_bytes s1
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (some { c0 := val, c1 := val1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        field.QM31 residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      field.QM31 residual

end PCVU_Fresh

open PCVU_Fresh AspisR1 AspisR1.CheckpointBytes3Word AspisR1.CheckpointBytes3ScalarShape AspisR1.CheckpointBytes3KDecode
open OraclePortCkptAbi2Extracted MultiproofConeCanonical

def lm (a b c d : Std.U8) : Std.U32 := core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d])
def dec_cm (x y : Std.U32) : Option field.CM31 :=
  if x >= field.P then none else if y >= field.P then none else some { a := x, b := y }
def dec_qm (c d : Option field.CM31) : Option field.QM31 :=
  match c with | none => none | some c => match d with | none => none | some d => some { c0 := c, c1 := d }

theorem fr_none (T : Type) : core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T none = ok none := by
  simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, massert, optionTag, read_discriminant]

theorem cm31_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) (h : [b0, b1, b2, b3, b4, b5, b6, b7].length ≤ Usize.max) :
    field.CM31.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7], h⟩ = ok (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) := by
  simp [field.CM31.from_le_bytes, field.M31.from_le_bytes, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, dec_cm, lm, Array.make]
  split <;> (try split) <;> simp_all [fr_none]

theorem qm31_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Std.U8) (h : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15].length ≤ Usize.max) :
    field.QM31.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], h⟩ =
      ok (dec_qm (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) (dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15))) := by
  simp [field.QM31.from_le_bytes, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, cm31_eq, dec_qm]
  generalize dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7) = c
  generalize dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15) = d
  cases c <;> cases d <;> simp [fr_none]

theorem lm_eq (a b c d : Std.U8) : lm a b c d = pack a b c d := PCVS_E32.lm_pack a b c d

theorem ge_P (x : Std.U32) : (x >= field.P) ↔ ¬ x.val < 2147483647 := by
  unfold field.P
  constructor <;> intro h <;> scalar_tac

theorem dec_eq (w0 w1 w2 w3 : Std.U32) :
    dec_qm (dec_cm w0 w1) (dec_cm w2 w3) =
      if Canonical (kWords w0 w1 w2 w3)
      then some (CheckpointBytes3Namespaces.fromK (kWords w0 w1 w2 w3)) else none := by
  by_cases h0 : w0.val < 2147483647 <;> by_cases h1 : w1.val < 2147483647 <;>
  by_cases h2 : w2.val < 2147483647 <;> by_cases h3 : w3.val < 2147483647 <;>
  simp [dec_qm, dec_cm, ge_P, Canonical, kWords, CheckpointBytes3Namespaces.fromK, h0, h1, h2, h3]

/-- Frozen QM31::from_le_bytes on a 16-byte window equals the canonical-limb test on the four little-endian words. -/
theorem fresh_shape (b : Slice Std.U8) (width : b.val.length = 16) :
    field.QM31.from_le_bytes b =
      if Canonical (kWords (word b width 0) (word b width 1) (word b width 2) (word b width 3))
      then ok (some (CheckpointBytes3Namespaces.fromK (kWords (word b width 0) (word b width 1) (word b width 2) (word b width 3))))
      else ok none := by
  obtain ⟨l, hl⟩ := b
  change l.length = 16 at width
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, ⟨b16, tl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> first | (exfalso; simp at width; done) | skip
  all_goals
    rw [qm31_eq, dec_eq]
    simp only [lm_eq]
    simp [word]
    split <;> rfl

theorem qm31_16 (b : Slice Std.U8) (width : b.val.length = 16) :
    field.QM31.from_le_bytes b = (do
      let q ← OraclePortCkptAbi2Extracted.decode_k_spec b
      ok (Option.map CheckpointBytes3Namespaces.fromK q)) := by
  have h0 : word_spec b 0#usize = ok (word b width 0) := by
    simpa [word] using word_total b 0#usize (by simp only [width]; scalar_tac)
  have h1 : word_spec b 4#usize = ok (word b width 1) := by
    simpa [word] using word_total b 4#usize (by simp only [width]; scalar_tac)
  have h2 : word_spec b 8#usize = ok (word b width 2) := by
    simpa [word] using word_total b 8#usize (by simp only [width]; scalar_tac)
  have h3 : word_spec b 12#usize = ok (word b width 3) := by
    simpa [word] using word_total b 12#usize (by simp only [width]; scalar_tac)
  rw [fresh_shape b width, k_shape b _ _ _ _ h0 h1 h2 h3]
  split <;> simp

/-- Window note: decode_k_spec carries no length check. For |b| <> 16 the frozen function indexes b[0..8] and b[8..16]
and panics (Result.fail) when |b| < 16, and ignores bytes past 16 when |b| > 16; the deployed decoder's behaviour off the 16-byte window
is not the frozen one (it reads word_spec at offsets 0,4,8,12 only), so only the window theorem is claimed. -/
#print axioms lm_eq
#print axioms ge_P
#print axioms dec_eq
#print axioms cm31_eq
#print axioms qm31_eq
#print axioms fresh_shape
#print axioms qm31_16
end PCVU_QM31
