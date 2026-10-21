import Query31ExplicitScanBody
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ExplicitScanConcreteSteps
open Query31ExplicitScanBody AspisV8R19.Q22WordScan

private theorem add_one_small (a : Std.Usize) (ha : a.val < 64) :
    ∃ b : Std.Usize, (a + 1#usize : Result Std.Usize) = .ok b ∧
      b.val = a.val + 1 := by
  have hb : a.val + 1 ≤ Usize.max := by
    have hm := Usize.cMax_bound_concrete.1
    omega
  have hs : (a + 1#usize : Result Std.Usize) ⦃ b => b.val = a.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using
      (show a.val + (1#usize).val ≤ Usize.max by simpa using hb)
  obtain ⟨b, hab, hv⟩ := Aeneas.Std.WP.spec_imp_exists hs
  exact ⟨b, hab, hv⟩

theorem active_q22_of_bounded_source (s : CurrentScan)
    (hlen : s.accepted_len.val < 22) (hdraws : s.draws.val < 64) :
    (q22StateOf s).accepted.length < 22 ∧ (q22StateOf s).draws < 64 := by
  constructor
  · have hp : (s.accepted.val.take s.accepted_len.val).length ≤ s.accepted_len.val :=
      List.length_take_le _ _
    have hval : (q22StateOf s).accepted.length =
        (s.accepted.val.take s.accepted_len.val).length := by
      simp [q22StateOf, acceptedPrefix]
    omega
  · simp [q22StateOf]
    exact hdraws

private theorem slice_read_prefix_success (s : CurrentScan)
    (hlen : s.accepted_len.val < 22) :
    ∃ sl : Slice Std.U32,
      core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32))
        s.accepted { «end» := s.accepted_len } = .ok sl ∧
      (↑sl : List Std.U32) = s.accepted.val.take s.accepted_len.val := by
  have h22 : (22#usize).val = 22 := rfl
  have hbound : s.accepted_len.val ≤ s.accepted.length := by
    simp only [Array.length, s.accepted.property, h22]
    omega
  have hs := core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    ({ «end» := s.accepted_len } : core.ops.range.RangeTo Std.Usize)
    (Array.to_slice s.accepted) hbound
  obtain ⟨sl, hrun, hspec⟩ := Aeneas.Std.WP.spec_imp_exists hs
  refine ⟨sl, ?_, ?_⟩
  · change core.slice.index.SliceIndexRangeToUsizeSlice.index
      { «end» := s.accepted_len } (Array.to_slice s.accepted) = .ok sl
    exact hrun
  · rcases hspec with ⟨hv, _⟩
    simpa [Array.to_slice, List.slice] using hv

private theorem anyM_u32_eq_mem (xs : List Std.U32) (candidate : Std.U32) :
    List.anyM (Aeneas.Std.core.cmp.PartialEqU32.eq candidate) xs =
      .ok (decide (candidate ∈ xs)) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.anyM_cons, Aeneas.Std.liftFun2, Aeneas.Std.core.cmp.impls.PartialEqU32.eq]
      by_cases heq : candidate = y
      · subst y
        change (Result.ok (decide (candidate = candidate)) >>= fun b =>
          if b = true then pure true else _) = Result.ok (decide (candidate ∈ candidate :: ys))
        simp
        rfl
      · simp [heq, ih]

theorem slice_contains_eq_mem (sl : Slice Std.U32) (candidate : Std.U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate =
      .ok (decide (candidate ∈ (↑sl : List Std.U32))) := by
  change List.anyM (Aeneas.Std.core.cmp.PartialEqU32.eq candidate)
    (↑sl : List Std.U32) = _
  exact anyM_u32_eq_mem (↑sl : List Std.U32) candidate

private theorem mem_map_val_iff (xs : List Std.U32) (candidate : Std.U32) :
    candidate.val ∈ xs.map (fun y => y.val) ↔ candidate ∈ xs := by
  constructor
  · intro h
    simp only [List.mem_map] at h
    obtain ⟨y, hy, hval⟩ := h
    have heq : candidate = y := by
      cases candidate with
      | mk cbv => cases y with
        | mk ybv =>
          simp only [Aeneas.Std.UScalar.mk.injEq]
          exact (BitVec.toNat_inj).mp hval.symm
    exact heq ▸ hy
  · intro h
    simp only [List.mem_map]
    exact ⟨candidate, h, rfl⟩

private theorem array_update_success_val {α : Type} {n : Usize}
    (v : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    ∃ a : Array α n, Array.update v i x = .ok a ∧
      a.val = v.val.set i.val x := by
  have hidx : i.val < v.val.length := by simpa [v.property] using hi
  let a : Array α n := ⟨v.val.set i.val x, by simp [List.length_set, v.property]⟩
  refine ⟨a, ?_, rfl⟩
  unfold Array.update
  change (match v.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some _ => Result.ok a) = Result.ok a
  rw [List.getElem?_eq_getElem hidx]

/-- The one-candidate fresh transition for the source-shaped body, with all
    five Std-operation slots instantiated by the actual Aeneas operations;
    only iterator advancement remains an explicit argument. -/
theorem fresh_from_bounds
    {Iter : Type} (next : Iter → Result (Option Std.U32 × Iter))
    (iter iter1 : Iter) (s : CurrentScan) (candidate : Std.U32)
    (hnext : next iter = .ok (some candidate, iter1))
    (hlen : s.accepted_len.val < 22) (hdraw : s.draws.val < 64)
    (hfresh : candidate.val ∉ acceptedPrefix s) :
    ∃ drawNext lenNext a,
      ((s.draws + 1#usize : Result Std.Usize) = .ok drawNext) ∧
      drawNext.val = s.draws.val + 1 ∧
      ((s.accepted_len + 1#usize : Result Std.Usize) = .ok lenNext) ∧
      lenNext.val = s.accepted_len.val + 1 ∧
      (s.accepted.update s.accepted_len candidate = .ok a) ∧
      body (stdOps next) iter s =
        .ok (.cont (iter1, { accepted := a, accepted_len := lenNext, draws := drawNext })) ∧
      q22StateOf { s with accepted := a, accepted_len := lenNext, draws := drawNext } =
        ⟨acceptedPrefix s ++ [candidate.val], s.draws.val + 1⟩ ∧
      scan (q22StateOf s) [candidate.val] =
        (q22StateOf { s with accepted := a, accepted_len := lenNext, draws := drawNext }, false) := by
  obtain ⟨drawNext, hdrawop, hdrawval⟩ := add_one_small s.draws hdraw
  obtain ⟨lenNext, hlenop, hlenval⟩ := add_one_small s.accepted_len (by omega)
  obtain ⟨sl, hsl, hslval⟩ := slice_read_prefix_success s hlen
  have hmem : candidate ∉ (↑sl : List Std.U32) := by
    rw [hslval]
    intro hm
    apply hfresh
    change candidate.val ∈ (s.accepted.val.take s.accepted_len.val).map (fun x => x.val)
    exact (mem_map_val_iff (s.accepted.val.take s.accepted_len.val) candidate).mpr hm
  have hcontains : core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate = .ok false := by
    rw [slice_contains_eq_mem]
    simp [hmem]
  have hupdSpec := Array.update_spec s.accepted s.accepted_len candidate (by
    have h22 : (22#usize).val = 22 := rfl
    simp only [Array.length, s.accepted.property, h22]
    omega)
  obtain ⟨a, hupdate, _⟩ := Aeneas.Std.WP.spec_imp_exists hupdSpec
  have hnotfull : s.accepted_len ≠ 22#usize := by
    intro he
    have hv := congrArg UScalar.val he
    simp at hv
    omega
  have hnotcap : s.draws ≠ 64#usize := by
    intro he
    have hv := congrArg UScalar.val he
    simp at hv
    omega
  have hmodel := active_q22_of_bounded_source s hlen hdraw
  have hstep := fresh_step_q22 (stdOps next) iter iter1 s candidate drawNext lenNext sl a
    hnext hnotfull hnotcap hdrawop hsl hcontains hupdate hupdate hlenop
    hmodel.1 hmodel.2 hfresh (by
      have h22 : (22#usize).val = 22 := rfl
      simp only [s.accepted.property, h22]
      omega) hlenval hdrawval
  have hstate := q22_state_fresh_update s candidate a lenNext drawNext hupdate
    (by
      have h22 : (22#usize).val = 22 := rfl
      simp only [s.accepted.property, h22]
      omega) hlenval hdrawval
  exact ⟨drawNext, lenNext, a, hdrawop, hdrawval, hlenop, hlenval,
    hupdate, hstep.1, hstate, hstep.2⟩

#print axioms fresh_from_bounds
#print axioms slice_read_prefix_success
#print axioms slice_contains_eq_mem
end Query31ExplicitScanConcreteSteps
