#!/bin/bash
# generates PRVEq_QM31_s1.lean from the PCVU_E001 emission (fresh text) plus the proof
set -e
cd "$(dirname "$0")"
OUT=${1:-PRVEq_QM31_s1.lean}
F=PCVU_E001_emitted/raw/PCVU_qm31/Funs.lean
P=$(printf '_ | ⟨b0, %s⟩' "$(python3 - <<'EOF'
s="⟨b16, tl⟩"
for i in range(15,0,-1): s="_ | ⟨b%d, %s⟩"%(i,s)
print(s)
EOF
)")
{
cat <<EOF
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
-- HAND MODEL (trust row HM-C Option/Result): the Option Try branch and from_residual, text as in R1CandidateFieldParsers (see PCVU_HAND_MODELS.json);
-- read_discriminant on Option Infallible resolves to AspisR1DecodeKHelperV7Bridge.optionInfallibleDiscriminantInst.
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} (self : Option T) :
  Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  := do
  match self with
  | none => ok (core.ops.control_flow.ControlFlow.Break none)
  | some v => ok (core.ops.control_flow.ControlFlow.Continue v)
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) (o : Option core.convert.Infallible) : Result (Option T) := do
  let i := read_discriminant o
  massert (i = 0#isize)
  ok none
EOF
sed -n '/^@\[global_simps, irreducible\] def field.P/,/^end PCVU_qm31/p' "$F" | grep -v '^end PCVU_qm31'
cat <<EOF
end PCVU_Fresh

open PCVU_Fresh AspisR1 AspisR1.CheckpointBytes3Word AspisR1.CheckpointBytes3ScalarShape AspisR1.CheckpointBytes3KDecode
open OraclePortCkptAbi2Extracted AspisR1.OraclePortCkptAbi4Decode MultiproofConeCanonical

def lm (a b c d : Std.U8) : Std.U32 := core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d])
def dec_cm (x y : Std.U32) : Option field.CM31 :=
  if x >= field.P then none else if y >= field.P then none else some { a := x, b := y }
def dec_qm (c d : Option field.CM31) : Option field.QM31 :=
  match c with | none => none | some c => match d with | none => none | some d => some { c0 := c, c1 := d }

theorem fr_none (T : Type) : core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T none = ok none := by
  simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, massert, read_discriminant, AspisR1DecodeKHelperV7Bridge.optionInfallibleDiscriminant]

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

theorem ge_P (x : Std.U32) : field.P.val ≤ x.val ↔ ¬ x.val < 2147483647 := by
  unfold field.P
  simp

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
  rcases l with $P <;> first | (exfalso; simp at width; done) | skip
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

-- Window note: decode_k_spec carries no length check. For |b| <> 16 the frozen function indexes b[0..8] and b[8..16]
-- and panics (Result.fail) when |b| < 16, and ignores bytes past 16 when |b| > 16; the deployed decoder's behaviour off the 16-byte window
-- is not the frozen one (it reads word_spec at offsets 0,4,8,12 only), so only the window theorem is claimed.
#print axioms lm_eq
#print axioms ge_P
#print axioms dec_eq
#print axioms cm31_eq
#print axioms qm31_eq
#print axioms fresh_shape
#print axioms qm31_16
end PCVU_QM31
EOF
} > "$OUT"
