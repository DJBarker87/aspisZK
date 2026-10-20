import S3ActualLoop0WithCompleteOperations
import S3ActualGroupTableTransfer
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

abbrev S := field.WideExact
abbrev E := AspisR1CurrentWide.Proof.E

def DecodedMeaning (a : Array S 12#usize) (f : Fin 12 → E) : Prop :=
  ∀ k : Fin 12, decode (a.val[k.val]'(by
    have hp := a.property
    change a.val.length = 12 at hp
    omega)) = f k

def modelGroup (n : Nat) : Fin 12 :=
  if h : n < 64 then
    ⟨actualGroupVal ⟨n, h⟩, actual_group_table_value_bound ⟨n, h⟩⟩
  else 0

def PrefixMeaning (input : Nat → E) (initial : Fin 12 → E) : Nat → Fin 12 → E
  | 0 => initial
  | n + 1 => fun k =>
      if k.val = (modelGroup n).val then
        PrefixMeaning input initial n (modelGroup n) + input n
      else PrefixMeaning input initial n k

theorem decoded_meaning_set (a : Array S 12#usize) (idx : Std.Usize)
    (v : S) (f : Fin 12 → E) (hmeaning : DecodedMeaning a f)
    (hidx : idx.val < 12) :
    DecodedMeaning (a.set idx v)
      (fun k => if k.val = idx.val then decode v else f k) := by
  cases a with
  | mk xs hxs =>
    intro k
    have hn : xs.length = 12 := by simpa using hxs
    have hidxList : idx.val < xs.length := by omega
    have hkList : k.val < xs.length := by omega
    change decode ((xs.set idx.val v)[k.val]'(by simpa [List.length_set, hxs])) = _
    rw [List.getElem_set (h := by simpa [List.length_set] using hkList)]
    by_cases hk : k.val = idx.val
    · simp [hk]
    · have hm := hmeaning k
      change decode (xs[k.val]'(by simpa using hkList)) = f k at hm
      have hne : idx.val ≠ k.val := fun h => hk h.symm
      rw [if_neg hne]
      change decode (xs[k.val]'(by simpa using hkList)) =
        (if k.val = idx.val then decode v else f k)
      rw [if_neg hk]
      exact hm

theorem canonical_set (a : Array S 12#usize) (idx : Std.Usize) (v : S)
    (hcanonical : CanonicalAccumulatorArray a) (hv : Canonical v)
    (hidx : idx.val < 12) : CanonicalAccumulatorArray (a.set idx v) := by
  cases a with
  | mk xs hxs =>
    intro k
    have hn : xs.length = 12 := by simpa using hxs
    have hkList : k.val < xs.length := by omega
    have hjSet : k.val < (xs.set idx.val v).length := by
      simp [List.length_set, hn]
      omega
    change Canonical ((xs.set idx.val v)[k.val]'hjSet)
    by_cases heq : idx.val = k.val
    · have hcell : (xs.set idx.val v)[k.val]'hjSet = v := by
        have hself := List.getElem_set_self (l := xs) (i := idx.val) (a := v)
          (by simpa [heq] using hjSet)
        simpa [heq] using hself
      rw [hcell]
      exact hv
    · have hcell : (xs.set idx.val v)[k.val]'hjSet = xs[k.val]'hkList := by
        simpa using (List.getElem_set_ne (l := xs) (i := idx.val) (j := k.val) heq hjSet)
      rw [hcell]
      simpa using hcanonical k

theorem actual_loop0_body_prefix_step
    (bytes : Slice Std.U8) (input : Nat → E)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : Array S 12#usize)
    (initial : Fin 12 → E)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (hstart : j.val = iter.start.val) (hj : j.val < 64)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hfield : ∃ x, decodeField bytes j = .ok x ∧ decode x = input j.val)
    (hmeaning : DecodedMeaning coefficients (PrefixMeaning input initial iter.start.val))
    (hcanonical : CanonicalAccumulatorArray coefficients) :
    ∃ updated,
      weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes iter coefficients =
        .ok (.cont (iterNext, updated)) ∧
      DecodedMeaning updated (PrefixMeaning input initial (iter.start.val + 1)) ∧
      CanonicalAccumulatorArray updated := by
  obtain ⟨inputCoeff, hfield, hinputModel⟩ := hfield
  -- The actual body readback and U8→Usize cast are exposed explicitly here.
  have htableBound : j.val < weights.S2_INACTIVE_GROUPS.length := by
    simpa [weights.S2_INACTIVE_GROUPS.property] using hj
  obtain ⟨groupByte, hgroup, _hgroupValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_GROUPS j htableBound)
  let group : Std.Usize := UScalar.cast .Usize groupByte
  have hcast : lift (UScalar.cast .Usize groupByte) = .ok group := rfl
  have hgroupBound := S3ActualGroupTableTransfer.actual_group_index_value_bound
    j hj groupByte hgroup
  have hcastEq : UScalar.cast .Usize groupByte = group := Result.ok.inj hcast
  have hgroupVal : group.val = groupByte.val := by
    simpa only [U8.cast_Usize_val_eq] using (congrArg UScalar.val hcastEq).symm
  have htableRead : groupByte.val = (modelGroup j.val).val := by
    have hlen : j.val < weights.S2_INACTIVE_GROUPS.length := by
      simpa [weights.S2_INACTIVE_GROUPS.property] using hj
    obtain ⟨selected, hselected, hvalue⟩ :=
      WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_GROUPS j hlen)
    have heq : selected = groupByte := Result.ok.inj (hselected.symm.trans hgroup)
    rw [← heq, hvalue]
    simp [modelGroup, actualGroupVal, hj]
  have hgroupModel : group.val = (modelGroup j.val).val := hgroupVal.trans htableRead
  have haccIndex : group.val < coefficients.length := by
    simpa [coefficients.property] using hgroupBound
  obtain ⟨oldCoeff, hold, holdValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec coefficients group haccIndex)
  have hOldCanonical : Canonical oldCoeff := by
    rw [holdValue]
    exact hcanonical ⟨group.val, hgroupBound⟩
  have hInputCanonical := decodeField_success_canonical bytes j inputCoeff hfield
  obtain ⟨newCoeff, hadd, hnewCanonical, haddValue⟩ :=
    add_total_exact oldCoeff inputCoeff hOldCanonical hInputCanonical
  obtain ⟨updated, hupdate, hset⟩ :=
    WP.spec_imp_exists (Array.update_spec coefficients group newCoeff haccIndex)
  have hbody := generated_loop0_body_success actualOperations bytes iter coefficients
    j iterNext groupByte group oldCoeff inputCoeff newCoeff updated
    hnext hgroup hcast hold hfield hadd hupdate
  have hsetMeaning := decoded_meaning_set coefficients group newCoeff
    (PrefixMeaning input initial iter.start.val)
    hmeaning hgroupBound
  have hsetCanonical := canonical_set coefficients group newCoeff hcanonical
    hnewCanonical hgroupBound
  have holdSem : decode oldCoeff =
      PrefixMeaning input initial iter.start.val (modelGroup iter.start.val) := by
    have hslot : oldCoeff = coefficients.val[(modelGroup iter.start.val).val]'(by
        have hp := coefficients.property
        change coefficients.val.length = 12 at hp
        omega) := by
      simpa [hgroupModel, hstart] using holdValue
    rw [hslot]
    exact hmeaning (modelGroup iter.start.val)
  have hnewSem : decode newCoeff =
      PrefixMeaning input initial iter.start.val (modelGroup iter.start.val) + input iter.start.val := by
    calc
      decode newCoeff = decode oldCoeff + decode inputCoeff := haddValue
      _ = PrefixMeaning input initial iter.start.val (modelGroup iter.start.val) +
          input iter.start.val := by rw [holdSem, hinputModel, hstart]
  have hfunction : ∀ k : Fin 12,
      (if k.val = group.val then decode newCoeff
        else PrefixMeaning input initial iter.start.val k) =
      PrefixMeaning input initial (iter.start.val + 1) k := by
    intro k
    rw [show iter.start.val + 1 = Nat.succ iter.start.val by omega, PrefixMeaning]
    rw [hgroupModel, hstart]
    by_cases hk : k.val = (modelGroup iter.start.val).val
    · simp [hk, hnewSem]
    · simp [hk]
  have hmeaningNext : DecodedMeaning updated
      (PrefixMeaning input initial (iter.start.val + 1)) := by
    rw [hset]
    intro k
    calc
      decode ((coefficients.set group newCoeff).val[k.val]'(by
        have hp := (coefficients.set group newCoeff).property
        change (coefficients.set group newCoeff).val.length = 12 at hp
        omega)) =
          (if k.val = group.val then decode newCoeff
            else PrefixMeaning input initial iter.start.val k) := hsetMeaning k
      _ = PrefixMeaning input initial (iter.start.val + 1) k := hfunction k
  have hcanonicalUpdated : CanonicalAccumulatorArray updated := by
    rw [hset]
    exact hsetCanonical
  exact ⟨updated, hbody, hmeaningNext, hcanonicalUpdated⟩

theorem actual_loop0_whole_prefix
    (bytes : Slice Std.U8) (input : Nat → E) (initialMeaning : Fin 12 → E)
    (iter0 : core.ops.range.Range Std.Usize)
    (initial : Array S 12#usize)
    (hstart : iter0.start.val = 0) (hend : iter0.end.val = 64)
    (hmeaning : DecodedMeaning initial (PrefixMeaning input initialMeaning 0))
    (hcanonical : CanonicalAccumulatorArray initial)
    (hfields : ∀ j : Std.Usize, j.val < 64 →
      ∃ x, decodeField bytes j = .ok x ∧ decode x = input j.val) :
    ∃ result,
      weights.s2_grouped_inactive_pair_loop0 actualOperations iter0 bytes initial = .ok result ∧
      DecodedMeaning result (PrefixMeaning input initialMeaning 64) ∧
      CanonicalAccumulatorArray result := by
  have hwp : WP.spec
      (weights.s2_grouped_inactive_pair_loop0 actualOperations iter0 bytes initial)
      (fun result => DecodedMeaning result (PrefixMeaning input initialMeaning 64) ∧
        CanonicalAccumulatorArray result) := by
    unfold weights.s2_grouped_inactive_pair_loop0
    refine loop.spec_decr_nat
      (fun s : core.ops.range.Range Std.Usize × Array S 12#usize => 64 - s.1.start.val)
      (fun s : core.ops.range.Range Std.Usize × Array S 12#usize =>
        s.1.start.val ≤ 64 ∧ s.1.end.val = 64 ∧
        DecodedMeaning s.2 (PrefixMeaning input initialMeaning s.1.start.val) ∧
        CanonicalAccumulatorArray s.2)
      (fun result => DecodedMeaning result (PrefixMeaning input initialMeaning 64) ∧
        CanonicalAccumulatorArray result)
      (fun s => weights.s2_grouped_inactive_pair_loop0.body actualOperations
        bytes s.1 s.2)
      (iter0, initial) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, coefficients⟩
      rcases hs with ⟨hbound, hendState, hmeaningState, hcanonicalState⟩
      by_cases hlt : iter.start.val < iter.end.val
      · have hnextSpec := core.iter.range.IteratorRange.next_'S_some_spec iter hlt
        obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases pair with ⟨opt, iterNext⟩
        rcases hpost with ⟨hopt, hnextStart, hnextEnd⟩
        have hopt' : opt = some iter.start := hopt
        subst opt
        have hj : iter.start.val < 64 := by rw [hendState] at hlt; exact hlt
        have hstep := actual_loop0_body_prefix_step bytes input
          iter coefficients initialMeaning iter.start iterNext rfl hj hnext
          (hfields iter.start hj) hmeaningState hcanonicalState
        rcases hstep with ⟨updated, hbody, hmeaningNext, hcanonicalNext⟩
        have hnextEndVal : iterNext.end.val = iter.end.val := congrArg UScalar.val hnextEnd
        rw [hbody, WP.spec_ok]
        change (iterNext.start.val ≤ 64 ∧ iterNext.end.val = 64 ∧
          DecodedMeaning updated (PrefixMeaning input initialMeaning iterNext.start.val) ∧
          CanonicalAccumulatorArray updated) ∧
          64 - iterNext.start.val < 64 - iter.start.val
        refine ⟨⟨?_, ?_, ?_, hcanonicalNext⟩, ?_⟩
        · rw [hnextStart]
          omega
        · rw [hnextEndVal, hendState]
        · simpa [hnextStart] using hmeaningNext
        · rw [hnextStart]
          omega
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hge64 : iter.start.val = 64 := by omega
        have hnextSpec := core.iter.range.IteratorRange.next_'S_none_spec iter hge
        obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases pair with ⟨opt, iterNext⟩
        rcases hpost with ⟨rfl, rfl⟩
        rw [weights.s2_grouped_inactive_pair_loop0.body, hnext]
        simp only [bind_tc_ok, WP.spec_ok]
        exact ⟨⟨by simpa [hge64] using hmeaningState, hcanonicalState⟩⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hstart]
        omega
      · exact hend
      · simpa [hstart] using hmeaning
      · exact hcanonical
  obtain ⟨result, hresult, hfinal⟩ := WP.spec_imp_exists hwp
  exact ⟨result, hresult, hfinal.1, hfinal.2⟩

end AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actual_loop0_body_prefix_step
#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actual_loop0_whole_prefix
