import AspisR1.CopyPatternInnerSource
import AspisR1.CopyPatternFoldModel
import CopyEndpointExact

/-! One actual pattern lane: bounded reads, scalar lift and checked field arithmetic.
The model descriptor comes from these same source arrays. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternLimbExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Pattern := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev decodedCells {n : Usize} (a : Array QM n) := AspisR1.CopyEndpointExact.decodedCells a

def cell {α : Type} {n : Usize} (a : Array α n) (i : Fin n.val) : α :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def modelPattern (pattern : Pattern)
    (hcolumns : ∀ j : Fin 16, (cell pattern.columns j).val < 16) : R0P.CopyPattern :=
  { kinds := fun j => (cell pattern.kinds j).val,
    columns := fun j => ⟨(cell pattern.columns j).val,hcolumns j⟩,
    offsets := fun j => (cell pattern.offsets j).val }

def runLimb (openings powers : Array QM 16#usize) (limb : Usize)
    (pattern : Pattern) (value : QM) : Result QM := do
  let kind ← Array.index_usize pattern.kinds limb
  if kind = 1#u8 then
    let column ← Array.index_usize pattern.columns limb
    let index ← lift (core.convert.num.FromUsizeU8.from column)
    let q ← Array.index_usize openings index
    let offset ← Array.index_usize pattern.offsets limb
    let lifted ← AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.lift_m31 offset
    let source ← field.QM31.add q lifted
    let power ← Array.index_usize powers limb
    let product ← field.QM31.mul power source
    field.QM31.add value product
  else ok value

theorem limb_success (openings powers : Array QM 16#usize) (limb : Usize)
    (pattern : Pattern) (value : QM) (hlimb : limb.val < 16)
    (hcolumns : ∀ j : Fin 16, (cell pattern.columns j).val < 16)
    (hoffsets : ∀ j : Fin 16, (cell pattern.offsets j).val < AspisR1.TerminalLiftM31Exact.P)
    (hopenings : CanonicalArray openings) (hpowers : CanonicalArray powers)
    (hvalue : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM value) :
    ∃ out, runLimb openings powers limb pattern value = .ok out ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      decode out = AspisR1.CopyPatternFoldModel.step (modelPattern pattern hcolumns)
        (decodedCells openings) (decodedCells powers) (decode value) ⟨limb.val,hlimb⟩ := by
  let j : Fin 16 := ⟨limb.val,hlimb⟩
  have hb : limb.val < (16#usize).val := by simpa using hlimb
  have hk : Array.index_usize pattern.kinds limb = .ok (cell pattern.kinds j) := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok pattern.kinds limb hb
  by_cases hkind : cell pattern.kinds j = 1#u8
  · have hkindVal : (cell pattern.kinds j).val = 1 := by rw [hkind]; rfl
    let column := cell pattern.columns j
    let index := core.convert.num.FromUsizeU8.from column
    let columnFin : Fin 16 := ⟨column.val,hcolumns j⟩
    have hindex : index.val = column.val := core.convert.num.FromUsizeU8.from_val_eq column
    have hib : index.val < (16#usize).val := by rw [hindex]; exact hcolumns j
    have hcolumn : Array.index_usize pattern.columns limb = .ok column :=
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok pattern.columns limb hb
    have hread : Array.index_usize openings index = .ok (cells openings columnFin) := by
      simpa [cells,columnFin,hindex] using
        AspisR1.ExtractedMaskHornerStep.array_index_usize_ok openings index hib
    have hoffset : Array.index_usize pattern.offsets limb = .ok (cell pattern.offsets j) :=
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok pattern.offsets limb hb
    have hpower : Array.index_usize powers limb = .ok (cells powers j) :=
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok powers limb hb
    obtain ⟨lifted,hlift,hclift,hvlift⟩ :=
      AspisR1.TerminalLiftM31Exact.lift_source_exact (cell pattern.offsets j) (hoffsets j)
    have hcopyLift : AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.lift_m31
        (cell pattern.offsets j) = .ok lifted := by
      simpa only [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.lift_m31,
        AspisR1CopyPatternCandidate.field.CM31.from_m31,
        AspisR1CopyPatternCandidate.field.QM31.from_cm31,
        AspisR1CopyPatternCandidate.field.CM31.ZERO,
        AspisR1CopyPatternCandidate.field.M31.ZERO,
        pool_v1.pair_forest_semantic_terminal.lift_m31,
        field.CM31.from_m31,field.QM31.from_cm31,field.CM31.ZERO,field.M31.ZERO,
        bind_tc_ok] using hlift
    change decode lifted = ((cell pattern.offsets j).val : ExactQM) at hvlift
    obtain ⟨source,hsource,hcsource,hvsource⟩ :=
      AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
        (cells openings columnFin) lifted (hopenings columnFin) hclift
    change decode source = decode (cells openings columnFin) + decode lifted at hvsource
    obtain ⟨product,hproduct,hcproduct,hvproduct⟩ :=
      AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact
        (cells powers j) source (hpowers j) hcsource
    change decode product = decode (cells powers j) * decode source at hvproduct
    obtain ⟨out,hout,hcout,hvout⟩ :=
      AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact value product hvalue hcproduct
    change decode out = decode value + decode product at hvout
    refine ⟨out,?_,hcout,?_⟩
    · dsimp only [index] at hread
      simp only [runLimb,hk,hkind,if_pos,hcolumn,lift,hread,hoffset,hcopyLift,
        hsource,hpower,hproduct,hout,bind_tc_ok]
    · change decode out = if (cell pattern.kinds j).val = 1 then
        decode value + decode (cells powers j) *
          (decode (cells openings columnFin) + ((cell pattern.offsets j).val : ExactQM))
        else decode value
      rw [if_pos hkindVal,hvout,hvproduct,hvsource,hvlift]
  · have hkindVal : (cell pattern.kinds j).val ≠ 1 := by
      intro he
      apply hkind
      apply UScalar.eq_of_val_eq
      exact he
    refine ⟨value,?_,hvalue,?_⟩
    · simp only [runLimb,hk,if_neg hkind,bind_tc_ok]
    · change decode value = if (cell pattern.kinds j).val = 1 then _ else decode value
      rw [if_neg hkindVal]

#print axioms limb_success
end
end AspisR1.CopyPatternLimbExact
