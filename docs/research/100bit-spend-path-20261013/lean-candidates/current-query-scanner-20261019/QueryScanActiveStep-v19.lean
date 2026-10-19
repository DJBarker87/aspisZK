import AspisR1QueryScan.Funs
import AspisV8R19.Q22WordScan
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript

def acceptedPrefix (s : QueryScan) : List Nat :=
  (s.accepted.val.take s.accepted_len.val).map (fun x => x.val)

private theorem take_set_succ {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) (x : α) :
    (xs.set i x).take (i + 1) = xs.take i ++ [x] := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hi
      | cons a tail => simp
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons a tail =>
          have hi' : i < tail.length := by simp at hi; omega
          simp [ih tail hi']


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

theorem acceptedPrefix_update_append
    (s : QueryScan) (candidate : Std.U32) (a : Array Std.U32 22#usize)
    (newLen : Std.Usize)
    (hupdate : a.val = s.accepted.val.set s.accepted_len.val candidate)
    (hnew : newLen.val = s.accepted_len.val + 1)
    (hbound : s.accepted_len.val < s.accepted.val.length) :
    acceptedPrefix { s with accepted := a, accepted_len := newLen } =
      acceptedPrefix s ++ [candidate.val] := by
  change (a.val.take newLen.val).map (fun x => x.val) =
    (s.accepted.val.take s.accepted_len.val).map (fun x => x.val) ++ [candidate.val]
  rw [hupdate, hnew, take_set_succ _ _ hbound]
  simp


private theorem anyM_u32_eq_mem (xs : List Std.U32) (candidate : Std.U32) :
    List.anyM (Aeneas.Std.core.cmp.PartialEqU32.eq candidate) xs =
      .ok (decide (candidate ∈ xs)) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.anyM_cons, Aeneas.Std.core.cmp.PartialEqU32,
        Aeneas.Std.liftFun2, Aeneas.Std.core.cmp.impls.PartialEqU32.eq]
      by_cases heq : candidate = y
      · subst y
        change (Result.ok (decide (candidate = candidate)) >>= fun b => if b = true then pure true else _) = Result.ok (decide (candidate ∈ candidate :: ys))
        simp
        rfl
      · simp [heq, ih]

theorem slice_contains_eq_mem (s : Slice Std.U32) (candidate : Std.U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 s candidate =
      .ok (decide (candidate ∈ (↑s : List Std.U32))) := by
  change List.anyM (Aeneas.Std.core.cmp.PartialEqU32.eq candidate) (↑s : List Std.U32) = _
  exact anyM_u32_eq_mem (↑s : List Std.U32) candidate

theorem mem_map_val_iff (xs : List Std.U32) (candidate : Std.U32) :
    candidate.val ∈ xs.map (fun y => y.val) ↔ candidate ∈ xs := by
  constructor
  · intro h
    simp only [List.mem_map] at h
    obtain ⟨y, hy, hval⟩ := h
    have heq : candidate = y := by
      cases candidate with
      | mk cbv =>
        cases y with
        | mk ybv =>
          simp only [Aeneas.Std.UScalar.mk.injEq]
          exact (BitVec.toNat_inj).mp hval.symm
    exact heq ▸ hy
  · intro h
    simp only [List.mem_map]
    exact ⟨candidate, h, rfl⟩

theorem scan_body_fresh_candidate
    (iter : core.array.iter.IntoIter U32 8#usize) (s : QueryScan)
    (candidate : Std.U32) (iter1 : core.array.iter.IntoIter U32 8#usize)
    (drawNext lenNext : Std.Usize) (sl : Slice Std.U32)
    (a : Array Std.U32 22#usize)
    (hnext : core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
      ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ QUERY_COUNT)
    (hnotcap : s.draws ≠ QUERY_MAX_DRAWS)
    (hdraw : s.draws + 1#usize = ok drawNext)
    (hsl : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      s.accepted { «end» := s.accepted_len } = ok sl)
    (hslval : (↑sl : List Std.U32) = s.accepted.val.take s.accepted_len.val)
    (hfresh : candidate.val ∉ acceptedPrefix s)
    (hupdate : s.accepted.update s.accepted_len candidate = ok a)
    (hlen : s.accepted_len + 1#usize = ok lenNext) :
    QueryScan.scan_loop.body iter s =
      ok (.cont (iter1, { accepted := a, accepted_len := lenNext, draws := drawNext })) := by
  have hmem : candidate ∉ (↑sl : List Std.U32) := by
    rw [hslval]
    intro hm
    apply hfresh
    change candidate.val ∈ (s.accepted.val.take s.accepted_len.val).map (fun x => x.val)
    exact (mem_map_val_iff (s.accepted.val.take s.accepted_len.val) candidate).mpr hm
  have hcontains : core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate = ok false := by
    rw [slice_contains_eq_mem]
    simp [hmem]
  simp [QueryScan.scan_loop.body, hnext, hnotfull, hnotcap, hdraw, hsl,
    hcontains, hupdate, hlen]

#print axioms array_update_success_val
#print axioms acceptedPrefix_update_append
#print axioms anyM_u32_eq_mem
#print axioms slice_contains_eq_mem
#print axioms mem_map_val_iff
#print axioms scan_body_fresh_candidate
open AspisV8R19.Q22WordScan

def q22StateOfFresh (s : QueryScan) : ScanState :=
  ⟨acceptedPrefix s, s.draws.val⟩

theorem q22_state_fresh_update
    (s : QueryScan) (candidate : Std.U32) (a : Array Std.U32 22#usize)
    (lenNext drawNext : Std.Usize)
    (hupdate : s.accepted.update s.accepted_len candidate = ok a)
    (hbound : s.accepted_len.val < s.accepted.val.length)
    (hlenval : lenNext.val = s.accepted_len.val + 1)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    q22StateOfFresh { s with accepted := a, accepted_len := lenNext, draws := drawNext } =
      ⟨acceptedPrefix s ++ [candidate.val], s.draws.val + 1⟩ := by
  have hbound' : s.accepted_len.val < (22#usize).val := by
    simpa [s.accepted.property] using hbound
  obtain ⟨a0, hupdate0, hset⟩ := array_update_success_val s.accepted s.accepted_len candidate hbound'
  have haa : a0 = a := Result.ok.inj (hupdate0.symm.trans hupdate)
  have hseta : a.val = s.accepted.val.set s.accepted_len.val candidate := by
    simpa [haa] using hset
  change (⟨(a.val.take lenNext.val).map (fun x => x.val), drawNext.val⟩ : ScanState) =
    ⟨acceptedPrefix s ++ [candidate.val], s.draws.val + 1⟩
  simp only [ScanState.mk.injEq]
  constructor
  · rw [hseta, hlenval, take_set_succ _ _ hbound]
    simp [acceptedPrefix]
  · exact hdrawval

theorem q22_scan_one_fresh (q : ScanState) (x : Nat)
    (hactive : q.accepted.length ≠ 22 ∧ q.draws ≠ 64)
    (hfresh : x ∉ q.accepted) :
    scan q [x] = (⟨q.accepted ++ [x], q.draws + 1⟩, false) := by
  simp [scan, keep, hactive.1, hactive.2, hfresh]

theorem scan_body_duplicate_candidate
    (iter : core.array.iter.IntoIter U32 8#usize) (s : QueryScan)
    (candidate : Std.U32) (iter1 : core.array.iter.IntoIter U32 8#usize)
    (drawNext : Std.Usize) (sl : Slice Std.U32)
    (hnext : core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
      ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ QUERY_COUNT)
    (hnotcap : s.draws ≠ QUERY_MAX_DRAWS)
    (hdraw : s.draws + 1#usize = ok drawNext)
    (hsl : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      s.accepted { «end» := s.accepted_len } = ok sl)
    (hslval : (↑sl : List Std.U32) = s.accepted.val.take s.accepted_len.val)
    (hmember : candidate.val ∈ acceptedPrefix s) :
    QueryScan.scan_loop.body iter s =
      ok (.cont (iter1, { accepted := s.accepted, accepted_len := s.accepted_len, draws := drawNext })) := by
  have hmem : candidate ∈ (↑sl : List Std.U32) := by
    rw [hslval]
    have hp : candidate.val ∈ (s.accepted.val.take s.accepted_len.val).map (fun x => x.val) := by
      simpa [acceptedPrefix] using hmember
    exact (mem_map_val_iff (s.accepted.val.take s.accepted_len.val) candidate).mp hp
  have hcontains : core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate = ok true := by
    rw [slice_contains_eq_mem]
    simp [hmem]
  simp [QueryScan.scan_loop.body, hnext, hnotfull, hnotcap, hdraw, hsl,
    hcontains]

theorem q22_state_duplicate_update
    (s : QueryScan) (drawNext : Std.Usize)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    q22StateOfFresh { s with draws := drawNext } =
      ⟨acceptedPrefix s, s.draws.val + 1⟩ := by
  simp [q22StateOfFresh, acceptedPrefix, hdrawval]

theorem q22_scan_one_duplicate (q : ScanState) (x : Nat)
    (hactive : q.accepted.length ≠ 22 ∧ q.draws ≠ 64)
    (hmember : x ∈ q.accepted) :
    scan q [x] = (⟨q.accepted, q.draws + 1⟩, false) := by
  simp [scan, keep, hactive.1, hactive.2, hmember]

#print axioms q22_state_fresh_update
#print axioms q22_scan_one_fresh
#print axioms scan_body_duplicate_candidate
#print axioms q22_state_duplicate_update
#print axioms q22_scan_one_duplicate
end AspisR1QueryScanUnrolled.r0_transcript
