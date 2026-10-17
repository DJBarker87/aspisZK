import AspisR1.PoseidonGroupSliceModel
import ExtractedMaskHornerStep
import AspisR1.PoseidonClosure2GroupCall
import AspisR1.PoseidonClosure2GroupRange
import AspisR1.PoseidonClosure2PackGroup
import ExtractedMaskQmPackBase4Whole

set_option autoImplicit false
namespace AspisR1.PoseidonClosure2GroupExact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1PoseidonProjectedClosure2Source

abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
private def get4 (a : Array QM 4#usize) (i : Usize) (hi : i.val < 4) : QM :=
  a.val[i.val]'(by simpa [a.property] using hi)
private def get3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def getPrepared3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩
abbrev Call := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

theorem actual_call_exact
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (internalArray : Array QM 16#usize)
    (blockPrepared : Prepared) (block : QM)
    (weightsPrepared : Array Prepared 3#usize) (weights : Array QM 3#usize)
    (leading : Array QM 4#usize) (full : Array QM 4#usize)
    (group : Usize) (hg : group.val < 4)
    (hblock : Canonical block)
    (hblockPrepared : PreparedFor blockPrepared block)
    (hweights : ∀ i : Fin 3, Canonical (get3 weights i))
    (hweightsPrepared : ∀ i : Fin 3, PreparedFor
      (getPrepared3 weightsPrepared i)
      (get3 weights i))
    (hsuccessor : ∀ i : Fin 16, Canonical
      (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt)))
    (hinternal : ∀ i : Fin 16, Canonical
      (internalArray.val[i.val]'(by simpa [internalArray.property] using i.isLt)))
    (hleading : ∀ (i : Usize) (hi : i.val < 4),
      Canonical (get4 leading i hi))
    (hfull : ∀ (i : Usize) (hi : i.val < 4),
      Canonical (get4 full i hi)) :
    ∃ out : QM,
      Call (openings, internalArray, blockPrepared, weightsPrepared, leading, full) group =
        .ok (out, (openings, internalArray, blockPrepared, weightsPrepared, leading, full)) ∧
      Canonical out ∧
      Decode out = Decode block *
        (Decode (get3 weights i0) *
            (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z ⟨group.val,hg⟩ -
              Decode (get4 leading group hg)) +
          Decode (get3 weights i1) *
            (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z ⟨group.val,hg⟩ -
              Decode (get4 full group hg)) +
          Decode (get3 weights i2) *
            (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z ⟨group.val,hg⟩ -
              AspisR1.PoseidonGroupSliceModel.packedGroup internalArray ⟨group.val,hg⟩)) := by
  obtain ⟨st0,en0,ss,hlenS,target,st1,en1,si,hlenI,internalPacked,
      leadValue,fullValue,q1,q3,q4,q5,out,
      hst0,hen0,hb0,hs0,hp0,hct0,hmodel0,
      hst1,hen1,hb1,hs1,hp1,hct1,hmodel1,
      hleadRead,hfullRead,hsub1,hsub3,hsub4,hqsum,hmul,houtcan,hmodel⟩ :=
    AspisR1.PoseidonClosure2GroupCall.closure2_call_mut_success
      openings internalArray blockPrepared block weightsPrepared weights leading full group hg
      hblock hblockPrepared hweights hweightsPrepared hsuccessor hinternal hleading hfull
  obtain ⟨start,finish,hrange,hstart,hfinish,hfinishBound⟩ :=
    AspisR1.PoseidonClosure2GroupRange.group_range_success group hg
  have hstartEq : start = st0 := by apply UScalar.eq_of_val_eq; omega
  have hfinishEq : finish = en0 := by apply UScalar.eq_of_val_eq; omega
  have hs0' : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) openings.succ_z
      { start, «end» := finish } = .ok ss := by
    rw [hstartEq, hfinishEq]
    exact hs0
  have hst1Eq : st1 = st0 := by apply UScalar.eq_of_val_eq; omega
  have hen1Eq : en1 = en0 := by apply UScalar.eq_of_val_eq; omega
  have hs1' : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) internalArray
      { start, «end» := finish } = .ok si := by
    rw [hstartEq, hfinishEq]
    simpa [hst1Eq, hen1Eq] using hs1
  have hmulSpec : (4#usize * group : Result Usize) ⦃ z => z.val = 4 * group.val ⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨start', hmulRun, hstart'⟩ := WP.spec_imp_exists hmulSpec
  have hstart'Eq : start' = start := by apply UScalar.eq_of_val_eq; omega
  rw [hstart'Eq] at hmulRun
  have haddSpec : (start + 4#usize : Result Usize) ⦃ z => z.val = start.val + 4 ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨finish', haddRun, hfinish'⟩ := WP.spec_imp_exists haddSpec
  have hfinish'Eq : finish' = finish := by apply UScalar.eq_of_val_eq; omega
  rw [hfinish'Eq] at haddRun
  have hs0Slice : core.slice.index.SliceIndexRangeUsizeSlice.index
      { start, «end» := finish } openings.succ_z.to_slice = .ok ss := by
    simpa only [Array.index_SliceIndexRangeUsizeSlice] using hs0'
  have hs1Slice : core.slice.index.SliceIndexRangeUsizeSlice.index
      { start, «end» := finish } internalArray.to_slice = .ok si := by
    simpa only [Array.index_SliceIndexRangeUsizeSlice] using hs1'
  have hcall : Call (openings, internalArray, blockPrepared, weightsPrepared, leading, full) group =
      .ok (out, (openings, internalArray, blockPrepared, weightsPrepared, leading, full)) := by
    simp [Call,
      AspisR1PoseidonProjectedClosure2Source.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
      hmulRun, haddRun, hs0Slice, hp0, hs1Slice, hp1, hleadRead, hsub1, hfullRead, hsub3, hsub4, hqsum, hmul]
  have htargetModel := AspisR1.PoseidonGroupSliceModel.source_pack_model
    openings.succ_z group hg st0 en0 ss hlenS target hst0 hen0 hb0 hs0 hmodel0
  have hinternalModel := AspisR1.PoseidonGroupSliceModel.source_pack_model
    internalArray group hg st1 en1 si hlenI internalPacked hst1 hen1 hb1 hs1 hmodel1
  have hgroupBound : group.val < (4#usize).val := by simpa using hg
  have hleadRun : Array.index_usize leading group = .ok (get4 leading group hg) := by
    simpa only [get4] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok leading group hgroupBound
  have hfullRun : Array.index_usize full group = .ok (get4 full group hg) := by
    simpa only [get4] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok full group hgroupBound
  rw [hleadRead] at hleadRun
  rw [hfullRead] at hfullRun
  have hleadValue : leadValue = get4 leading group hg := Result.ok.inj hleadRun
  have hfullValue : fullValue = get4 full group hg := Result.ok.inj hfullRun
  refine ⟨out,hcall,houtcan,?_⟩
  change Decode out = Decode block *
    (Decode (get3 weights i0) * (Decode target - Decode leadValue) +
      Decode (get3 weights i1) * (Decode target - Decode fullValue) +
      Decode (get3 weights i2) * (Decode target - Decode internalPacked)) at hmodel
  change Decode target = AspisR1.PoseidonGroupSliceModel.packedGroup
    openings.succ_z ⟨group.val,hg⟩ at htargetModel
  change Decode internalPacked = AspisR1.PoseidonGroupSliceModel.packedGroup
    internalArray ⟨group.val,hg⟩ at hinternalModel
  rw [htargetModel,hinternalModel,hleadValue,hfullValue] at hmodel
  exact hmodel

#print axioms actual_call_exact

end AspisR1.PoseidonClosure2GroupExact
