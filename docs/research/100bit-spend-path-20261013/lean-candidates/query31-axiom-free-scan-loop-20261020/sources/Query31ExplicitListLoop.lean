import Query31ExplicitScanConcreteSteps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ExplicitListLoop
open Query31ExplicitScanBody Query31ExplicitScanConcreteSteps
open AspisV8R19.Q22WordScan

abbrev CurrentScan := Query31ExplicitScanBody.CurrentScan

def listNext : List Std.U32 → Result (Option Std.U32 × List Std.U32)
  | [] => .ok (none, [])
  | x :: xs => .ok (some x, xs)

def step (p : List Std.U32 × CurrentScan) :
    Result (ControlFlow (List Std.U32 × CurrentScan) (CurrentScan × Option Bool)) :=
  body (stdOps listNext) p.1 p.2

def scanListLoop (xs : List Std.U32) (s : CurrentScan) :
    Result (CurrentScan × Option Bool) := Aeneas.Std.loop step (xs, s)

private theorem take_set_succ {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) (x : α) :
    (xs.set i x).take (i + 1) = xs.take i ++ [x] := by
  induction i generalizing xs with
  | zero => cases xs with | nil => simp at hi | cons a tail => simp
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

theorem q22_state_fresh_update
    (s : CurrentScan) (candidate : Std.U32) (a : Array Std.U32 22#usize)
    (lenNext drawNext : Std.Usize)
    (hupdate : s.accepted.update s.accepted_len candidate = .ok a)
    (hbound : s.accepted_len.val < s.accepted.val.length)
    (hlenval : lenNext.val = s.accepted_len.val + 1)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    q22StateOf { s with accepted := a, accepted_len := lenNext, draws := drawNext } =
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

private theorem q22_state_duplicate_update (s : CurrentScan) (drawNext : Std.Usize)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    q22StateOf { s with draws := drawNext } =
      ⟨acceptedPrefix s, s.draws.val + 1⟩ := by
  simp [q22StateOf, acceptedPrefix, hdrawval]

def validState (s : CurrentScan) : Prop :=
  s.accepted_len.val ≤ 22 ∧ s.draws.val ≤ 64 ∧
    (acceptedPrefix s).length = s.accepted_len.val

theorem validState_of_bounds (s : CurrentScan)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64) : validState s := by
  refine ⟨hlen, hdraw, ?_⟩
  have harray : s.accepted.val.length = 22 := by
    simpa using s.accepted.property
  simp [acceptedPrefix, harray, Nat.min_eq_left hlen]

private theorem active_q22 (s : CurrentScan) (h : validState s)
    (hactive : s.accepted_len.val < 22 ∧ s.draws.val < 64) :
    (q22StateOf s).accepted.length ≠ 22 ∧ (q22StateOf s).draws ≠ 64 := by
  constructor
  · have hs : (q22StateOf s).accepted.length = s.accepted_len.val := by
      simpa [q22StateOf] using h.2.2
    omega
  · simp [q22StateOf]
    omega

private theorem add_one_small_local (a : Std.Usize) (ha : a.val < 64) :
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

private theorem duplicate_from_bounds
    (iter iter1 : List Std.U32) (s : CurrentScan) (candidate : Std.U32)
    (hnext : listNext iter = .ok (some candidate, iter1))
    (hlen : s.accepted_len.val < 22) (hdraw : s.draws.val < 64)
    (hmember : candidate.val ∈ acceptedPrefix s) :
    ∃ drawNext,
      (s.draws + 1#usize : Result Std.Usize) = .ok drawNext ∧
      drawNext.val = s.draws.val + 1 ∧
      body (stdOps listNext) iter s =
        .ok (.cont (iter1, { s with draws := drawNext })) ∧
      q22StateOf { s with draws := drawNext } =
        ⟨acceptedPrefix s, s.draws.val + 1⟩ := by
  obtain ⟨drawNext, hdrawop, hdrawval⟩ := add_one_small_local s.draws hdraw
  obtain ⟨sl, hsl, hslval⟩ := slice_read_prefix_success s hlen
  have hmem : candidate ∈ (↑sl : List Std.U32) := by
    rw [hslval]
    have hp : candidate.val ∈
        (s.accepted.val.take s.accepted_len.val).map (fun x => x.val) := by
      simpa [acceptedPrefix] using hmember
    exact (mem_map_val_iff (s.accepted.val.take s.accepted_len.val) candidate).mp hp
  have hcontains : core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate = .ok true := by
    rw [slice_contains_eq_mem]
    simp [hmem]
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
  have hstep := duplicate_step (stdOps listNext) iter iter1 s candidate drawNext sl
    hnext hnotfull hnotcap hdrawop hsl hcontains
  have hstate := q22_state_duplicate_update s drawNext hdrawval
  exact ⟨drawNext, hdrawop, hdrawval, hstep, hstate⟩

private theorem q22_scan_continuation (s s' : ScanState) (x : Nat)
    (xs : List Nat)
    (hstop : ¬(s.accepted.length = 22 ∨ s.draws = 64))
    (hkeep : keep s.accepted x = s'.accepted)
    (hdraw : s.draws + 1 = s'.draws) :
    scan s (x :: xs) = scan s' xs := by
  simp [scan, hstop, hkeep, hdraw]

private theorem scanListLoop_empty (s : CurrentScan) :
    scanListLoop [] s = .ok (s, some false) := by
  unfold scanListLoop step
  rw [Aeneas.Std.loop.eq_def]
  simp [body, stdOps, listNext]

private theorem scanListLoop_cons_cont
    (x : Std.U32) (xs : List Std.U32) (s s' : CurrentScan)
    (hbody : body (stdOps listNext) (x :: xs) s = .ok (.cont (xs, s'))) :
    scanListLoop (x :: xs) s = scanListLoop xs s' := by
  unfold scanListLoop step
  rw [Aeneas.Std.loop.eq_def]
  simp only [hbody]

def optionStop : Option Bool → Bool
  | none => true
  | some b => b

/-- The list-backed iterator model for the actual source-shaped body refines
    Q22's scan recurrence. This keeps array `IntoIter` out of the trusted import
    closure; the generated body/source equivalence and the array-iterator
    boundary remain separate. -/
theorem scanListLoop_q22 : ∀ (xs : List Std.U32) (s : CurrentScan),
    validState s → ∃ sf pending,
      scanListLoop xs s = .ok (sf, pending) ∧
      scan (q22StateOf s) (xs.map (fun x => x.val)) =
        (q22StateOf sf, optionStop pending) := by
  intro xs
  induction xs with
  | nil =>
      intro s hs
      refine ⟨s, some false, scanListLoop_empty s, ?_⟩
      simp [optionStop, scan]
  | cons x xs ih =>
      intro s hs
      by_cases hlen : s.accepted_len.val = 22
      · have hlenEq : s.accepted_len = 22#usize := by
          apply UScalar.eq_of_val_eq
          simpa using hlen
        have hnext : listNext (x :: xs) = .ok (some x, xs) := rfl
        have hbody : body (stdOps listNext) (x :: xs) s =
            .ok (.done (s, none)) := by
          simp [body, stdOps, hnext, hlenEq]
        have hloop : scanListLoop (x :: xs) s = .ok (s, none) := by
          unfold scanListLoop step
          rw [Aeneas.Std.loop.eq_def]
          simp only [hbody]
        refine ⟨s, none, hloop, ?_⟩
        have hq : (q22StateOf s).accepted.length = 22 := by
          change (acceptedPrefix s).length = 22
          have hp := hs.2.2
          omega
        simp [optionStop, scan, hq]
      · by_cases hdraw : s.draws.val = 64
        · have hdrawEq : s.draws = 64#usize := by
            apply UScalar.eq_of_val_eq
            simpa using hdraw
          have hnext : listNext (x :: xs) = .ok (some x, xs) := rfl
          have hbody : body (stdOps listNext) (x :: xs) s =
              .ok (.done (s, none)) := by
            simp [body, stdOps, hnext, hlen, hdrawEq]
          have hloop : scanListLoop (x :: xs) s = .ok (s, none) := by
            unfold scanListLoop step
            rw [Aeneas.Std.loop.eq_def]
            simp only [hbody]
          refine ⟨s, none, hloop, ?_⟩
          have hq : (q22StateOf s).draws = 64 := by
            simpa [q22StateOf] using hdraw
          simp [optionStop, scan, hq]
        · have hlenBound := hs.1
          have hlenLt : s.accepted_len.val < 22 := by omega
          have hdrawBound := hs.2.1
          have hdrawLt : s.draws.val < 64 := by omega
          have hnext : listNext (x :: xs) = .ok (some x, xs) := rfl
          by_cases hfresh : x.val ∉ acceptedPrefix s
          · obtain ⟨drawNext, lenNext, a, hdrawop, hdrawval, hlenop, hlenval,
              hupdate, hbody, hstate, hscan⟩ :=
              fresh_from_bounds listNext (x :: xs) xs s x hnext hlenLt hdrawLt hfresh
            let s' : CurrentScan := ⟨a, lenNext, drawNext⟩
            have hvalid' : validState s' := by
              refine ⟨?_, ?_, ?_⟩
              · change lenNext.val ≤ 22
                omega
              · change drawNext.val ≤ 64
                omega
              · have hprefix := congrArg (fun q : ScanState => q.accepted.length) hstate
                change (acceptedPrefix s').length = lenNext.val
                calc
                  (acceptedPrefix s').length = (acceptedPrefix s).length + 1 := by
                    simpa [s', q22StateOf] using hprefix
                  _ = lenNext.val := by rw [hs.2.2, hlenval]
            obtain ⟨sf, pending, htail, hqtail⟩ := ih s' hvalid'
            have hloop := scanListLoop_cons_cont x xs s s' (by simpa [s'] using hbody)
            have hqstep : scan (q22StateOf s) (x.val :: xs.map (fun y => y.val)) =
                scan (q22StateOf s') (xs.map (fun y => y.val)) := by
              have hstop : ¬((q22StateOf s).accepted.length = 22 ∨
                  (q22StateOf s).draws = 64) := by
                exact not_or.mpr (active_q22 s hs ⟨hlenLt, hdrawLt⟩)
              have hstate' : q22StateOf s' =
                  ⟨acceptedPrefix s ++ [x.val], s.draws.val + 1⟩ := by
                simpa [s'] using hstate
              have hkeep : keep (q22StateOf s).accepted x.val = (q22StateOf s').accepted := by
                have hacc := congrArg (fun t : ScanState => t.accepted) hstate'
                change keep (acceptedPrefix s) x.val = (q22StateOf s').accepted
                rw [hacc]
                simp [keep, hfresh]
              have hdraw' : (q22StateOf s).draws + 1 = (q22StateOf s').draws := by
                have hh := congrArg (fun t : ScanState => t.draws) hstate'
                simpa [q22StateOf] using hh.symm
              exact q22_scan_continuation (q22StateOf s) (q22StateOf s') x.val
                (xs.map fun y => y.val) hstop hkeep hdraw'
            refine ⟨sf, pending, ?_, ?_⟩
            · rw [hloop, htail]
            · rw [List.map_cons, hqstep, hqtail]
          · have hmember : x.val ∈ acceptedPrefix s := by
              by_contra hn
              exact hfresh hn
            obtain ⟨drawNext, hdrawop, hdrawval, hbody, hstate⟩ :=
              duplicate_from_bounds (x :: xs) xs s x hnext hlenLt hdrawLt hmember
            let s' : CurrentScan := { s with draws := drawNext }
            have hvalid' : validState s' := by
              refine ⟨?_, ?_, ?_⟩
              · change s.accepted_len.val ≤ 22
                exact hs.1
              · change drawNext.val ≤ 64
                omega
              · change (acceptedPrefix s).length = s.accepted_len.val
                exact hs.2.2
            obtain ⟨sf, pending, htail, hqtail⟩ := ih s' hvalid'
            have hloop := scanListLoop_cons_cont x xs s s' (by simpa [s'] using hbody)
            have hqstep : scan (q22StateOf s) (x.val :: xs.map (fun y => y.val)) =
                scan (q22StateOf s') (xs.map (fun y => y.val)) := by
              have hstop : ¬((q22StateOf s).accepted.length = 22 ∨
                  (q22StateOf s).draws = 64) := by
                exact not_or.mpr (active_q22 s hs ⟨hlenLt, hdrawLt⟩)
              have hstate' : q22StateOf s' = ⟨acceptedPrefix s, s.draws.val + 1⟩ := by
                simpa [s'] using hstate
              have hkeep : keep (q22StateOf s).accepted x.val = (q22StateOf s').accepted := by
                have hacc := congrArg (fun t : ScanState => t.accepted) hstate'
                change keep (acceptedPrefix s) x.val = (q22StateOf s').accepted
                rw [hacc]
                simp [keep, hmember]
              have hdraw' : (q22StateOf s).draws + 1 = (q22StateOf s').draws := by
                have hh := congrArg (fun t : ScanState => t.draws) hstate'
                simpa [q22StateOf] using hh.symm
              exact q22_scan_continuation (q22StateOf s) (q22StateOf s') x.val
                (xs.map fun y => y.val) hstop hkeep hdraw'
            refine ⟨sf, pending, ?_, ?_⟩
            · rw [hloop, htail]
            · rw [List.map_cons, hqstep, hqtail]

#print axioms scanListLoop_q22
end Query31ExplicitListLoop
