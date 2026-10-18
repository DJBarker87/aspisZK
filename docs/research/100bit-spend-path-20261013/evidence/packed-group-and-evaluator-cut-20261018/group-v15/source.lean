import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalPackedFieldSource
import PoseidonExternalPackedModel
import ExtractedMaskQmPackBase4Arithmetic
import AspisR1.PoseidonGroupSliceModel
import ExtractedMaskConstants
import ExtractedMaskHornerStep
import ExtractedMaskTowerAdd
import AspisR1.PoseidonFullRoundCellStep
import R0P.Poseidon

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result WP
namespace AspisR1.PoseidonExternalPackedGroupCall
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonGroupSliceModel
open AspisR1.PoseidonExternalPackedModel
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisV8R15.ExactTowerBase (P)

abbrev State := Array field.QM31 16#usize
abbrev Packed := Array field.QM31 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def packedCell (a : Packed) (j : Fin 4) : field.QM31 :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

def packedCanonical (a : Packed) : Prop := ∀ j : Fin 4, CanonicalQM (packedCell a j)

def packedModel (state : State) (g : Fin 4) : Exact :=
  R0P.poseidonPackingFormula iBasis uBasis
    (R0P.poseidonMat4 (fun r => Decode (cell state (lane g r))))

def groupInput (state : State) (g : Fin 4) : Array field.QM31 4#usize :=
  Array.make 4#usize
    [cell state (lane g 0), cell state (lane g 1),
     cell state (lane g 2), cell state (lane g 3)]

def groupStep (state : State) (packed : Packed) (group : Usize) :
    Result (Packed × Usize) := do
  let start ← 4#usize * group
  let q0 ← Array.index_usize state start
  let i1 ← start + 1#usize
  let q1 ← Array.index_usize state i1
  let i2 ← start + 2#usize
  let q2 ← Array.index_usize state i2
  let i3 ← start + 3#usize
  let q3 ← Array.index_usize state i3
  let output ← state_only_poseidon.external_local_packed
    (Array.make 4#usize [q0,q1,q2,q3])
  let packed1 ← Array.update packed group output
  let group1 ← group + 1#usize
  ok (packed1,group1)

private theorem read_value (state : State) (index : Usize) (q : field.QM31)
    (hindex : index.val < 16) (hread : Array.index_usize state index = .ok q) :
    q = cell state ⟨index.val,hindex⟩ := by
  have hspec : Array.index_usize state index =
      .ok (cell state (⟨index.val,hindex⟩ : Fin 16)) := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state index
      (by simpa [state.property] using hindex)
  exact Result.ok.inj (hread.symm.trans hspec)

theorem groupStep_success (state : State) (packed : Packed) (g : Fin 4)
    (hstate : CanonicalState state) (hpacked : packedCanonical packed) :
    ∃ packed1 : Packed, ∃ group1 : Usize,
      groupStep state packed (UScalar.ofNatCore g.val (by have := g.isLt; scalar_tac)) =
        .ok (packed1,group1) ∧
      packedCanonical packed1 ∧
      (∀ j : Fin 4, Decode (packedCell packed1 j) =
        if j.val = g.val then packedModel state g else Decode (packedCell packed j)) ∧
      group1.val = g.val + 1 := by
  let group : Usize := UScalar.ofNatCore g.val (by have := g.isLt; scalar_tac)
  have hg : group.val = g.val := by simp [group,UScalar.ofNatCore_val_eq]
  have hglt : group.val < 4 := by rw [hg]; exact g.isLt
  have hmulSpec : (4#usize * group : Result Usize)
      ⦃z => z.val = 4 * group.val⦄ := by
    apply UScalar.mul_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨start,hmul,hstart⟩ := WP.spec_imp_exists hmulSpec
  have hstartVal : start.val = 4 * g.val := by rw [hstart,hg]
  have hplus1Spec : (start + 1#usize : Result Usize)
      ⦃z => z.val = start.val + 1⦄ := by
    apply UScalar.add_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨i1,hplus1,hi1⟩ := WP.spec_imp_exists hplus1Spec
  have hplus2Spec : (start + 2#usize : Result Usize)
      ⦃z => z.val = start.val + 2⦄ := by
    apply UScalar.add_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨i2,hplus2,hi2⟩ := WP.spec_imp_exists hplus2Spec
  have hplus3Spec : (start + 3#usize : Result Usize)
      ⦃z => z.val = start.val + 3⦄ := by
    apply UScalar.add_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨i3,hplus3,hi3⟩ := WP.spec_imp_exists hplus3Spec
  have h0bound : start.val < 16 := by rw [hstartVal]; omega
  have h1bound : i1.val < 16 := by rw [hi1,hstartVal]; omega
  have h2bound : i2.val < 16 := by rw [hi2,hstartVal]; omega
  have h3bound : i3.val < 16 := by rw [hi3,hstartVal]; omega
  have hread0 : Array.index_usize state start =
      .ok (cell state (lane g 0)) := by
    have h := AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok
      state start h0bound
    have heq : (⟨start.val,h0bound⟩ : Fin 16) = lane g 0 := by
      apply Fin.ext
      simp [lane,hstartVal]
    change Array.index_usize state start =
      .ok (cell state (⟨start.val,h0bound⟩ : Fin 16)) at h
    simpa only [heq] using h
  have hread1 : Array.index_usize state i1 =
      .ok (cell state (lane g 1)) := by
    have h := AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok
      state i1 h1bound
    have heq : (⟨i1.val,h1bound⟩ : Fin 16) = lane g 1 := by
      apply Fin.ext
      simp [lane,hi1,hstartVal]
    change Array.index_usize state i1 =
      .ok (cell state (⟨i1.val,h1bound⟩ : Fin 16)) at h
    simpa only [heq] using h
  have hread2 : Array.index_usize state i2 =
      .ok (cell state (lane g 2)) := by
    have h := AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok
      state i2 h2bound
    have heq : (⟨i2.val,h2bound⟩ : Fin 16) = lane g 2 := by
      apply Fin.ext
      simp [lane,hi2,hstartVal]
    change Array.index_usize state i2 =
      .ok (cell state (⟨i2.val,h2bound⟩ : Fin 16)) at h
    simpa only [heq] using h
  have hread3 : Array.index_usize state i3 =
      .ok (cell state (lane g 3)) := by
    have h := AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok
      state i3 h3bound
    have heq : (⟨i3.val,h3bound⟩ : Fin 16) = lane g 3 := by
      apply Fin.ext
      simp [lane,hi3,hstartVal]
    change Array.index_usize state i3 =
      .ok (cell state (⟨i3.val,h3bound⟩ : Fin 16)) at h
    simpa only [heq] using h
  have hcan0 : CanonicalQM (cell state (lane g 0)) := hstate (lane g 0)
  have hcan1 : CanonicalQM (cell state (lane g 1)) := hstate (lane g 1)
  have hcan2 : CanonicalQM (cell state (lane g 2)) := hstate (lane g 2)
  have hcan3 : CanonicalQM (cell state (lane g 3)) := hstate (lane g 3)
  let input := groupInput state g
  have hinput : input = Array.make 4#usize
      [cell state (lane g 0),cell state (lane g 1),
       cell state (lane g 2),cell state (lane g 3)] := rfl
  have hinputCan : ∀ r : Fin 4, CanonicalQM (input.val[r.val]'(by
      simpa [input.property] using r.isLt)) := by
    intro r
    fin_cases r <;> simp [input,groupInput,Array.make] <;> assumption
  obtain ⟨output,hcall,houtputCan,houtputModel⟩ :=
    AspisR1.PoseidonExternalLocalPackedFieldSource.external_local_packed_source_success
      input hinputCan
  have hinputModel :
      (fun r : Fin 4 => Decode
        (AspisR1.PoseidonExternalLocalPackedInputDecode.inputCell input r)) =
      (fun r : Fin 4 => Decode (cell state (lane g r))) := by
    funext r
    fin_cases r <;> rfl
  have hmodel : Decode output = packedModel state g := by
    change Decode output = R0P.poseidonPackingFormula iBasis uBasis
      (R0P.poseidonMat4 (fun r => Decode (cell state (lane g r))))
    exact houtputModel.trans
      (congrArg (fun v : Fin 4 → Exact =>
        R0P.poseidonPackingFormula iBasis uBasis (R0P.poseidonMat4 v)) hinputModel)
  change state_only_poseidon.external_local_packed
    (Array.make 4#usize [cell state (lane g 0), cell state (lane g 1),
      cell state (lane g 2), cell state (lane g 3)]) = .ok output at hcall
  obtain ⟨packed1,hupdate,hset⟩ := WP.spec_imp_exists
    (Array.update_spec packed group output (by
      have : group.val < packed.val.length := by
        simpa [packed.property] using hglt
      exact this))
  have hwrite : Array.update packed group output = .ok (packed.set group output) := by
    rw [hupdate,hset]
  have hincSpec : (group + 1#usize : Result Usize)
      ⦃z => z.val = group.val + 1⦄ := by
    apply UScalar.add_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨group1,hinc,hincVal⟩ := WP.spec_imp_exists hincSpec
  refine ⟨packed1,group1, ?_, ?_, ?_, ?_⟩
  · change groupStep state packed group = .ok (packed1, group1)
    simp [groupStep,hmul,hread0,hplus1,hread1,hplus2,hread2,hplus3,hread3,
      hcall,hupdate,hinc,bind_tc_ok]
  · intro j
    rw [hset]
    change CanonicalQM (cell (packed.set group output) j)
    rw [AspisR1.PoseidonFullRoundCellStep.cell_set]
    by_cases hj : j.val = group.val
    · simpa only [if_pos hj] using houtputCan
    · simpa only [if_neg hj, packedCell, cell] using hpacked j
  · intro j
    rw [hset]
    change Decode (cell (packed.set group output) j) = _
    rw [AspisR1.PoseidonFullRoundCellStep.cell_set]
    simp only [hg]
    by_cases hj : j.val = g.val
    · simpa only [if_pos hj] using hmodel
    · simp only [if_neg hj]
      rfl
  · rw [hincVal,hg]

#print axioms groupStep_success
end AspisR1.PoseidonExternalPackedGroupCall
