import AspisR1.PoseidonClosure2PackGroup
import AspisR1.PoseidonClosure2SubExact
import AspisR1.PoseidonPreparedSum3ActualValue
import AspisR1.PoseidonPreparedStateUnique
import PoseidonProjectedClosure2Source
import ExtractedMaskPreparedMul
import ExtractedMaskPreparedState
import ExtractedMaskTowerAdd

set_option autoImplicit false
namespace AspisR1.PoseidonClosure2GroupCall
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1PoseidonProjectedClosure2Source
open AspisV8R15.ExactTowerBase

abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Call := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

private def get4 (a : Array QM 4#usize) (i : Usize) (hi : i.val < 4) : QM :=
  a.val[i.val]'(by
    change i.val < a.val.length
    have hlen : a.val.length = 4 := by simpa using a.property
    rw [hlen]
    exact hi)
private def get3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def getPrepared3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

theorem closure2_call_mut_success
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (internalArray : Array QM 16#usize)
    (blockPrepared : Prepared) (block : QM)
    (weightsPrepared : Array Prepared 3#usize) (weights : Array QM 3#usize)
    (leading : Array QM 4#usize) (full : Array QM 4#usize)
    (group : Usize) (hg : group.val < 4)
    (hblock : Canonical block)
    (hblockPrepared : PreparedFor blockPrepared block)
    (hweights : ∀ i : Fin 3, Canonical (get3 weights i))
    (hweightsPrepared : ∀ i : Fin 3, PreparedFor (getPrepared3 weightsPrepared i) (get3 weights i))
    (hsuccessor : ∀ i : Fin 16, Canonical (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt)))
    (hinternal : ∀ i : Fin 16, Canonical (internalArray.val[i.val]'(by simpa [internalArray.property] using i.isLt)))
    (hleading : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 leading i hi))
    (hfull : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 full i hi)) :
    ∃ st0 en0 : Usize, ∃ ss : Slice QM, ∃ hlenS : ss.length = 4, ∃ target : QM,
    ∃ st1 en1 : Usize, ∃ si : Slice QM, ∃ hlenI : si.length = 4, ∃ internalPacked : QM,
    ∃ leadValue fullValue q1 q3 q4 q5 out : QM,
      st0.val = 4 * group.val ∧ en0.val = st0.val + 4 ∧ en0.val ≤ 16 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice QM)) openings.succ_z
        { start := st0, «end» := en0 } = .ok ss ∧
      field.qm31_pack_base4 ss = .ok target ∧ Canonical target ∧
      AspisR1.ExtractedMaskQM31Exact.decode target =
        AspisR1.PoseidonClosure2PackGroup.MappedPack
          (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt ss hlenS) ∧
      st1.val = 4 * group.val ∧ en1.val = st1.val + 4 ∧ en1.val ≤ 16 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice QM)) internalArray
        { start := st1, «end» := en1 } = .ok si ∧
      field.qm31_pack_base4 si = .ok internalPacked ∧ Canonical internalPacked ∧
      AspisR1.ExtractedMaskQM31Exact.decode internalPacked =
        AspisR1.PoseidonClosure2PackGroup.MappedPack
          (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt si hlenI) ∧
      Array.index_usize leading group = .ok leadValue ∧
      Array.index_usize full group = .ok fullValue ∧
      field.QM31.sub target leadValue = .ok q1 ∧
      field.QM31.sub target fullValue = .ok q3 ∧
      field.QM31.sub target internalPacked = .ok q4 ∧
      AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared weightsPrepared
        (Array.make 3#usize [q1,q3,q4]) = .ok q5 ∧
      field.PreparedQm31Multiplier.mul blockPrepared q5 = .ok out ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM out ∧
      Decode out = Decode block * (Decode (get3 weights i0) * (Decode target - Decode leadValue) +
        Decode (get3 weights i1) * (Decode target - Decode fullValue) +
        Decode (get3 weights i2) * (Decode target - Decode internalPacked)) := by
  obtain ⟨st0,en0,ss, target, hlenS, hst0, hen0, hb0, hs0, hp0, hct0, hmodel0⟩ :=
    AspisR1.PoseidonClosure2PackGroup.pack_group_success openings.succ_z group hg hsuccessor
  obtain ⟨st1,en1,si, internalPacked, hlenI, hst1, hen1, hb1, hs1, hp1, hct1, hmodel1⟩ :=
    AspisR1.PoseidonClosure2PackGroup.pack_group_success internalArray group hg hinternal
  have hstartEq : st0 = st1 := by apply UScalar.eq_of_val_eq; omega
  have hendEq : en0 = en1 := by apply UScalar.eq_of_val_eq; omega
  have htargetCanon : Canonical target := hct0
  have hinternalCanon : Canonical internalPacked := hct1
  have hleadBound : group.val < leading.length := by
    change group.val < leading.val.length
    have hl : leading.val.length = 4 := by simpa using leading.property
    rw [hl]
    exact hg
  have hleadRead := WP.spec_imp_exists (Array.index_usize_spec leading group hleadBound)
  obtain ⟨leadValue, hleadRead, hleadValue⟩ := hleadRead
  have hfullBound : group.val < full.length := by
    change group.val < full.val.length
    have hl : full.val.length = 4 := by simpa using full.property
    rw [hl]
    exact hg
  have hfullRead := WP.spec_imp_exists (Array.index_usize_spec full group hfullBound)
  obtain ⟨fullValue, hfullRead, hfullValue⟩ := hfullRead
  have hleadCanon : Canonical leadValue := by
    have hi : group.val < leading.val.length := by
      have hl : leading.val.length = 4 := by simpa using leading.property
      rw [hl]
      exact hg
    have hc := hleading group hg
    simpa [get4, hleadValue] using hc
  have hfullCanon : Canonical fullValue := by
    have hi : group.val < full.val.length := by
      have hl : full.val.length = 4 := by simpa using full.property
      rw [hl]
      exact hg
    have hc := hfull group hg
    simpa [get4, hfullValue] using hc
  obtain ⟨q1,hsub1,hq1can,hq1model⟩ := AspisR1.PoseidonClosure2SubExact.qm_sub_decode target leadValue htargetCanon hleadCanon
  obtain ⟨q3,hsub3,hq3can,hq3model⟩ := AspisR1.PoseidonClosure2SubExact.qm_sub_decode target fullValue htargetCanon hfullCanon
  obtain ⟨q4,hsub4,hq4can,hq4model⟩ := AspisR1.PoseidonClosure2SubExact.qm_sub_decode target internalPacked htargetCanon hinternalCanon
  have hprepared : ∀ i : Fin 3, ∃ x : QM, AspisR1.ExtractedMaskTowerAdd.CanonicalQM x ∧ PreparedFor (getPrepared3 weightsPrepared i) x := by
    intro i
    exact ⟨get3 weights i, hweights i, hweightsPrepared i⟩
  have hright : ∀ i : Fin 3, Canonical
      ((Array.make 3#usize [q1,q3,q4]).val[i.val]'(by scalar_tac)) := by
    intro i
    fin_cases i <;> simp [Array.make, hq1can, hq3can, hq4can]
  obtain ⟨q5,x0,x1,x2,hqsum,hq5can,hp0',hp1',hp2',hq5model⟩ :=
    AspisR1.PoseidonPreparedSum3ActualValue.actual_sum3_value weightsPrepared
      (Array.make 3#usize [q1,q3,q4]) hprepared hright
  have hx0 : x0 = get3 weights i0 :=
    AspisR1.PoseidonPreparedStateUnique.preparedFor_unique (getPrepared3 weightsPrepared i0)
      x0 (get3 weights i0) hp0' (hweightsPrepared i0)
  have hx1 : x1 = get3 weights i1 :=
    AspisR1.PoseidonPreparedStateUnique.preparedFor_unique (getPrepared3 weightsPrepared i1)
      x1 (get3 weights i1) hp1' (hweightsPrepared i1)
  have hx2 : x2 = get3 weights i2 :=
    AspisR1.PoseidonPreparedStateUnique.preparedFor_unique (getPrepared3 weightsPrepared i2)
      x2 (get3 weights i2) hp2' (hweightsPrepared i2)
  obtain ⟨out,hmul,houtcan,hmulmodel⟩ :=
    AspisR1.ExtractedMaskPreparedMul.prepared_mul_exact blockPrepared block q5 hblock hq5can hblockPrepared
  rw [hx0, hx1, hx2] at hq5model
  have hqsumValue : Decode q5 = Decode (get3 weights i0) * Decode q1 +
      Decode (get3 weights i1) * Decode q3 + Decode (get3 weights i2) * Decode q4 := by
    convert hq5model using 1 <;> rfl
  have hq1global : Decode q1 = Decode target - Decode leadValue := by
    simpa [Decode, AspisR1.PoseidonClosure2SubExact.Decode] using hq1model
  have hq3global : Decode q3 = Decode target - Decode fullValue := by
    simpa [Decode, AspisR1.PoseidonClosure2SubExact.Decode] using hq3model
  have hq4global : Decode q4 = Decode target - Decode internalPacked := by
    simpa [Decode, AspisR1.PoseidonClosure2SubExact.Decode] using hq4model
  have hmodel : Decode out = Decode block * (Decode (get3 weights i0) * (Decode target - Decode leadValue) +
        Decode (get3 weights i1) * (Decode target - Decode fullValue) +
        Decode (get3 weights i2) * (Decode target - Decode internalPacked)) := by
    change AspisR1.ExtractedMaskQM31Exact.decode out =
      AspisR1.ExtractedMaskQM31Exact.decode block * _
    rw [hmulmodel]
    change AspisR1.ExtractedMaskQM31Exact.decode block * Decode q5 = _
    rw [hqsumValue, hq1global, hq3global, hq4global]
  refine ⟨st0,en0,ss,hlenS,target,st1,en1,si,hlenI,internalPacked,
    leadValue,fullValue,q1,q3,q4,q5,out,
    hst0,hen0,hb0,hs0,hp0,hct0,hmodel0,
    hst1,hen1,hb1,hs1,hp1,hct1,hmodel1,
    hleadRead,hfullRead,hsub1,hsub3,hsub4,hqsum,hmul,houtcan,hmodel⟩

end AspisR1.PoseidonClosure2GroupCall
