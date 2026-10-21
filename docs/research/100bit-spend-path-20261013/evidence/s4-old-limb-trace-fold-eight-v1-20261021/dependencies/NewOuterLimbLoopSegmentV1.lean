import NewTermLoopOldLoopTransferV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsNewOuterLimbLoopSegmentV1

abbrev Usize := Std.Usize
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsNewTermBodyLinearBoundV1.Ops
abbrev LimbBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body
abbrev LimbLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem result_bind_assoc {α β γ : Type} (m : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do let y ← (do let x ← m; f x); g y) =
      (do let x ← m; let y ← f x; g y) := by
  cases m <;> rfl

def foldSegment (sums limbs : Array U64 8#usize) (limb : Usize) : Result (Array U64 8#usize) := do
  let x ← Array.index_usize sums limb
  let low ← lift (x &&& 2147483647#u64)
  let high ← x >>> 31#i32
  let part ← low + high
  let old ← Array.index_usize limbs limb
  let new ← old + part
  Array.update limbs limb new


private def limbStep (ops : Ops) (sums : Array U64 8#usize) :
    (Range × Array U64 8#usize) → Result (ControlFlow (Range × Array U64 8#usize)
      (Array U64 8#usize)) := fun s => LimbBody ops sums s.1 s.2

private theorem loop_success_of_eight_steps {α β : Type}
    (step : α → Result (ControlFlow α β)) (s0 s1 s2 s3 s4 s5 s6 s7 s8 : α)
    (out : β)
    (h0 : step s0 = .ok (.cont s1)) (h1 : step s1 = .ok (.cont s2))
    (h2 : step s2 = .ok (.cont s3)) (h3 : step s3 = .ok (.cont s4))
    (h4 : step s4 = .ok (.cont s5)) (h5 : step s5 = .ok (.cont s6))
    (h6 : step s6 = .ok (.cont s7)) (h7 : step s7 = .ok (.cont s8))
    (hdone : step s8 = .ok (.done out)) :
    Aeneas.Std.loop step s0 = .ok out := by
  rw [Aeneas.Std.loop.eq_def, h0]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h1]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h2]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h3]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h4]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h5]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h6]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h7]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, hdone]

private theorem range_next_none_success (iter : Range)
    (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
  have hltSpec : ∀ x y : Usize,
      core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  have hnot : ¬ iter.start.val < iter.end.val := by omega
  simp only [hnot, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hnone, hstart⟩, hend⟩
  have hi : iter' = iter := by
    cases iter with
    | mk iterStart iterEnd =>
      cases iter' with
      | mk start stop =>
        have hs : start = iterStart := hstart
        have he : stop = iterEnd := hend
        subst start; subst stop; rfl
  have hnext : core.iter.range.IteratorRange.next
      (core.iter.range.UScalarStep UScalarTy.Usize core.clone.CloneUsize
        core.cmp.PartialOrdUsize) iter = .ok (none, iter) := by
    rw [hrun, hnone, hi]
  simpa only [core.iter.range.StepUsize] using hnext

private theorem range_next_success (iter : Range)
    (hlt : iter.start.val < iter.end.val) :
    ∃ iter',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter') ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
    intro x; rfl
  have hltSpec : ∀ x y : Usize,
      core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
    intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  simp only [hlt, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hopt, hadvance⟩, hend⟩
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') := by rw [hrun, hopt]
  exact ⟨iter', hnext, hadvance, hend⟩

theorem old_limb_body_success_of_fold_segment
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize) (limb : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some limb, iter'))
    (hlimb : limb = iter.start)
    (hsegment : foldSegment sums limbs limb = .ok limbs') :
    LimbBody ops sums iter limbs = .ok (.cont (iter', limbs')) := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (ControlFlow.done limbs)
    | some limb => do
      let x ← Array.index_usize sums limb
      let low ← lift (x &&& 2147483647#u64)
      let high ← x >>> 31#i32
      let part ← low + high
      let old ← Array.index_usize limbs limb
      let new ← old + part
      let updated ← Array.update limbs limb new
      ok (ControlFlow.cont (iter1, updated))) = .ok (.cont (iter', limbs'))
  rw [hnext]
  simp only [bind_tc_ok]
  subst limb
  unfold foldSegment at hsegment
  obtain ⟨x, hx, hrest⟩ := bind_success _ _ _ hsegment
  obtain ⟨low, hlow, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨high, hhigh, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨part, hpart, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨new, hnew, hupdate⟩ := bind_success _ _ _ hrest
  simpa only [hx, hlow, hhigh, hpart, hold, hnew, hupdate, bind_tc_ok]


/-- Exact eight-cell fold emitted by the v6 batch-body suffix. This keeps the
    order of index, mask, shift, add, old-cell read, sum, and update calls. -/
def foldEight (sums limbs : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let i2 ← Array.index_usize sums 0#usize
  let i3 ← lift (i2 &&& 2147483647#u64)
  let i4 ← i2 >>> 31#i32
  let i5 ← i3 + i4
  let i6 ← Array.index_usize limbs 0#usize
  let i7 ← i6 + i5
  let limbs1 ← Array.update limbs 0#usize i7
  let i8 ← Array.index_usize sums 1#usize
  let i9 ← lift (i8 &&& 2147483647#u64)
  let i10 ← i8 >>> 31#i32
  let i11 ← i9 + i10
  let i12 ← Array.index_usize limbs1 1#usize
  let i13 ← i12 + i11
  let limbs2 ← Array.update limbs1 1#usize i13
  let i14 ← Array.index_usize sums 2#usize
  let i15 ← lift (i14 &&& 2147483647#u64)
  let i16 ← i14 >>> 31#i32
  let i17 ← i15 + i16
  let i18 ← Array.index_usize limbs2 2#usize
  let i19 ← i18 + i17
  let limbs3 ← Array.update limbs2 2#usize i19
  let i20 ← Array.index_usize sums 3#usize
  let i21 ← lift (i20 &&& 2147483647#u64)
  let i22 ← i20 >>> 31#i32
  let i23 ← i21 + i22
  let i24 ← Array.index_usize limbs3 3#usize
  let i25 ← i24 + i23
  let limbs4 ← Array.update limbs3 3#usize i25
  let i26 ← Array.index_usize sums 4#usize
  let i27 ← lift (i26 &&& 2147483647#u64)
  let i28 ← i26 >>> 31#i32
  let i29 ← i27 + i28
  let i30 ← Array.index_usize limbs4 4#usize
  let i31 ← i30 + i29
  let limbs5 ← Array.update limbs4 4#usize i31
  let i32 ← Array.index_usize sums 5#usize
  let i33 ← lift (i32 &&& 2147483647#u64)
  let i34 ← i32 >>> 31#i32
  let i35 ← i33 + i34
  let i36 ← Array.index_usize limbs5 5#usize
  let i37 ← i36 + i35
  let limbs6 ← Array.update limbs5 5#usize i37
  let i38 ← Array.index_usize sums 6#usize
  let i39 ← lift (i38 &&& 2147483647#u64)
  let i40 ← i38 >>> 31#i32
  let i41 ← i39 + i40
  let i42 ← Array.index_usize limbs6 6#usize
  let i43 ← i42 + i41
  let limbs7 ← Array.update limbs6 6#usize i43
  let i44 ← Array.index_usize sums 7#usize
  let i45 ← lift (i44 &&& 2147483647#u64)
  let i46 ← i44 >>> 31#i32
  let i47 ← i45 + i46
  let i48 ← Array.index_usize limbs7 7#usize
  let i49 ← i48 + i47
  Array.update limbs7 7#usize i49

private theorem emitted_fold_segment_success {β : Type}
    (sums limbs : Array U64 8#usize) (limb : Usize)
    (k : Array U64 8#usize → Result β) (out : β)
    (h : (do
      let x ← Array.index_usize sums limb
      let low ← lift (x &&& 2147483647#u64)
      let high ← x >>> 31#i32
      let part ← low + high
      let old ← Array.index_usize limbs limb
      let new ← old + part
      let updated ← Array.update limbs limb new
      k updated) = .ok out) :
    ∃ updated, foldSegment sums limbs limb = .ok updated ∧ k updated = .ok out := by
  obtain ⟨x, hx, hrest⟩ := bind_success _ _ _ h
  obtain ⟨low, hlow, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨high, hhigh, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨part, hpart, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨new, hnew, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨updated, hupdate, htail⟩ := bind_success _ _ _ hrest
  have hsegment : foldSegment sums limbs limb = .ok updated := by
    unfold foldSegment
    simp only [hx, hlow, hhigh, hpart, hold, hnew, hupdate, bind_tc_ok]
  exact ⟨updated, hsegment, htail⟩

/-- A successful exact v6 suffix can be split into eight named single-limb
    fold operations without changing evaluation order. -/
theorem foldEight_success_segments
    (sums limbs out : Array U64 8#usize)
    (h : foldEight sums limbs = .ok out) :
    ∃ l1 l2 l3 l4 l5 l6 l7,
      foldSegment sums limbs 0#usize = .ok l1 ∧
      foldSegment sums l1 1#usize = .ok l2 ∧
      foldSegment sums l2 2#usize = .ok l3 ∧
      foldSegment sums l3 3#usize = .ok l4 ∧
      foldSegment sums l4 4#usize = .ok l5 ∧
      foldSegment sums l5 5#usize = .ok l6 ∧
      foldSegment sums l6 6#usize = .ok l7 ∧
      foldSegment sums l7 7#usize = .ok out := by
  unfold foldEight at h
  obtain ⟨l1, h0, hrest⟩ := emitted_fold_segment_success sums limbs 0#usize
    (fun l1 => do
      let i8 ← Array.index_usize sums 1#usize
      let i9 ← lift (i8 &&& 2147483647#u64)
      let i10 ← i8 >>> 31#i32
      let i11 ← i9 + i10
      let i12 ← Array.index_usize l1 1#usize
      let i13 ← i12 + i11
      let l2 ← Array.update l1 1#usize i13
      let i14 ← Array.index_usize sums 2#usize
      let i15 ← lift (i14 &&& 2147483647#u64)
      let i16 ← i14 >>> 31#i32
      let i17 ← i15 + i16
      let i18 ← Array.index_usize l2 2#usize
      let i19 ← i18 + i17
      let l3 ← Array.update l2 2#usize i19
      let i20 ← Array.index_usize sums 3#usize
      let i21 ← lift (i20 &&& 2147483647#u64)
      let i22 ← i20 >>> 31#i32
      let i23 ← i21 + i22
      let i24 ← Array.index_usize l3 3#usize
      let i25 ← i24 + i23
      let l4 ← Array.update l3 3#usize i25
      let i26 ← Array.index_usize sums 4#usize
      let i27 ← lift (i26 &&& 2147483647#u64)
      let i28 ← i26 >>> 31#i32
      let i29 ← i27 + i28
      let i30 ← Array.index_usize l4 4#usize
      let i31 ← i30 + i29
      let l5 ← Array.update l4 4#usize i31
      let i32 ← Array.index_usize sums 5#usize
      let i33 ← lift (i32 &&& 2147483647#u64)
      let i34 ← i32 >>> 31#i32
      let i35 ← i33 + i34
      let i36 ← Array.index_usize l5 5#usize
      let i37 ← i36 + i35
      let l6 ← Array.update l5 5#usize i37
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out h
  obtain ⟨l2, h1, hrest⟩ := emitted_fold_segment_success sums l1 1#usize
    (fun l2 => do
      let i14 ← Array.index_usize sums 2#usize
      let i15 ← lift (i14 &&& 2147483647#u64)
      let i16 ← i14 >>> 31#i32
      let i17 ← i15 + i16
      let i18 ← Array.index_usize l2 2#usize
      let i19 ← i18 + i17
      let l3 ← Array.update l2 2#usize i19
      let i20 ← Array.index_usize sums 3#usize
      let i21 ← lift (i20 &&& 2147483647#u64)
      let i22 ← i20 >>> 31#i32
      let i23 ← i21 + i22
      let i24 ← Array.index_usize l3 3#usize
      let i25 ← i24 + i23
      let l4 ← Array.update l3 3#usize i25
      let i26 ← Array.index_usize sums 4#usize
      let i27 ← lift (i26 &&& 2147483647#u64)
      let i28 ← i26 >>> 31#i32
      let i29 ← i27 + i28
      let i30 ← Array.index_usize l4 4#usize
      let i31 ← i30 + i29
      let l5 ← Array.update l4 4#usize i31
      let i32 ← Array.index_usize sums 5#usize
      let i33 ← lift (i32 &&& 2147483647#u64)
      let i34 ← i32 >>> 31#i32
      let i35 ← i33 + i34
      let i36 ← Array.index_usize l5 5#usize
      let i37 ← i36 + i35
      let l6 ← Array.update l5 5#usize i37
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  obtain ⟨l3, h2, hrest⟩ := emitted_fold_segment_success sums l2 2#usize
    (fun l3 => do
      let i20 ← Array.index_usize sums 3#usize
      let i21 ← lift (i20 &&& 2147483647#u64)
      let i22 ← i20 >>> 31#i32
      let i23 ← i21 + i22
      let i24 ← Array.index_usize l3 3#usize
      let i25 ← i24 + i23
      let l4 ← Array.update l3 3#usize i25
      let i26 ← Array.index_usize sums 4#usize
      let i27 ← lift (i26 &&& 2147483647#u64)
      let i28 ← i26 >>> 31#i32
      let i29 ← i27 + i28
      let i30 ← Array.index_usize l4 4#usize
      let i31 ← i30 + i29
      let l5 ← Array.update l4 4#usize i31
      let i32 ← Array.index_usize sums 5#usize
      let i33 ← lift (i32 &&& 2147483647#u64)
      let i34 ← i32 >>> 31#i32
      let i35 ← i33 + i34
      let i36 ← Array.index_usize l5 5#usize
      let i37 ← i36 + i35
      let l6 ← Array.update l5 5#usize i37
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  obtain ⟨l4, h3, hrest⟩ := emitted_fold_segment_success sums l3 3#usize
    (fun l4 => do
      let i26 ← Array.index_usize sums 4#usize
      let i27 ← lift (i26 &&& 2147483647#u64)
      let i28 ← i26 >>> 31#i32
      let i29 ← i27 + i28
      let i30 ← Array.index_usize l4 4#usize
      let i31 ← i30 + i29
      let l5 ← Array.update l4 4#usize i31
      let i32 ← Array.index_usize sums 5#usize
      let i33 ← lift (i32 &&& 2147483647#u64)
      let i34 ← i32 >>> 31#i32
      let i35 ← i33 + i34
      let i36 ← Array.index_usize l5 5#usize
      let i37 ← i36 + i35
      let l6 ← Array.update l5 5#usize i37
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  obtain ⟨l5, h4, hrest⟩ := emitted_fold_segment_success sums l4 4#usize
    (fun l5 => do
      let i32 ← Array.index_usize sums 5#usize
      let i33 ← lift (i32 &&& 2147483647#u64)
      let i34 ← i32 >>> 31#i32
      let i35 ← i33 + i34
      let i36 ← Array.index_usize l5 5#usize
      let i37 ← i36 + i35
      let l6 ← Array.update l5 5#usize i37
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  obtain ⟨l6, h5, hrest⟩ := emitted_fold_segment_success sums l5 5#usize
    (fun l6 => do
      let i38 ← Array.index_usize sums 6#usize
      let i39 ← lift (i38 &&& 2147483647#u64)
      let i40 ← i38 >>> 31#i32
      let i41 ← i39 + i40
      let i42 ← Array.index_usize l6 6#usize
      let i43 ← i42 + i41
      let l7 ← Array.update l6 6#usize i43
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  obtain ⟨l7, h6, hrest⟩ := emitted_fold_segment_success sums l6 6#usize
    (fun l7 => do
      let i44 ← Array.index_usize sums 7#usize
      let i45 ← lift (i44 &&& 2147483647#u64)
      let i46 ← i44 >>> 31#i32
      let i47 ← i45 + i46
      let i48 ← Array.index_usize l7 7#usize
      let i49 ← i48 + i47
      Array.update l7 7#usize i49) out hrest
  have h7 : foldSegment sums l7 7#usize = .ok out := by
    simpa [foldSegment] using hrest
  exact ⟨l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7⟩


/-- The exact eight emitted coordinate folds execute the old loop1 body over
    the literal range 0..8, preserving the returned array. -/
theorem foldEight_success_old_limb_loop
    (ops : Ops) (sums limbs out : Array U64 8#usize)
    (hfold : foldEight sums limbs = .ok out) :
    LimbLoop ops { start := 0#usize, «end» := 8#usize } limbs sums = .ok out := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    foldEight_success_segments sums limbs out hfold
  let r0 : Range := { start := 0#usize, «end» := 8#usize }
  let r1 : Range := { start := 1#usize, «end» := 8#usize }
  let r2 : Range := { start := 2#usize, «end» := 8#usize }
  let r3 : Range := { start := 3#usize, «end» := 8#usize }
  let r4 : Range := { start := 4#usize, «end» := 8#usize }
  let r5 : Range := { start := 5#usize, «end» := 8#usize }
  let r6 : Range := { start := 6#usize, «end» := 8#usize }
  let r7 : Range := { start := 7#usize, «end» := 8#usize }
  let r8 : Range := { start := 8#usize, «end» := 8#usize }
  obtain ⟨t1, hn0, ha0, he0⟩ := range_next_success r0 (by simp [r0])
  have ht1 : t1 = r1 := by
    cases t1 with
    | mk st en =>
      have hs : st = 1#usize := UScalar.eq_of_val_eq (by simpa [r0] using ha0)
      have hend : en = 8#usize := by simpa [r0] using he0
      subst st; subst en; rfl
  have hn0r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r0 =
      .ok (some (0#usize), r1) := by simpa [r0, ht1] using hn0
  obtain ⟨t2, hn1, ha1, he1⟩ := range_next_success r1 (by simp [r1])
  have ht2 : t2 = r2 := by
    cases t2 with
    | mk st en =>
      have hs : st = 2#usize := UScalar.eq_of_val_eq (by simpa [r1] using ha1)
      have hend : en = 8#usize := by simpa [r1] using he1
      subst st; subst en; rfl
  have hn1r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r1 =
      .ok (some (1#usize), r2) := by simpa [r1, ht2] using hn1
  obtain ⟨t3, hn2, ha2, he2⟩ := range_next_success r2 (by simp [r2])
  have ht3 : t3 = r3 := by
    cases t3 with
    | mk st en =>
      have hs : st = 3#usize := UScalar.eq_of_val_eq (by simpa [r2] using ha2)
      have hend : en = 8#usize := by simpa [r2] using he2
      subst st; subst en; rfl
  have hn2r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r2 =
      .ok (some (2#usize), r3) := by simpa [r2, ht3] using hn2
  obtain ⟨t4, hn3, ha3, he3⟩ := range_next_success r3 (by simp [r3])
  have ht4 : t4 = r4 := by
    cases t4 with
    | mk st en =>
      have hs : st = 4#usize := UScalar.eq_of_val_eq (by simpa [r3] using ha3)
      have hend : en = 8#usize := by simpa [r3] using he3
      subst st; subst en; rfl
  have hn3r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r3 =
      .ok (some (3#usize), r4) := by simpa [r3, ht4] using hn3
  obtain ⟨t5, hn4, ha4, he4⟩ := range_next_success r4 (by simp [r4])
  have ht5 : t5 = r5 := by
    cases t5 with
    | mk st en =>
      have hs : st = 5#usize := UScalar.eq_of_val_eq (by simpa [r4] using ha4)
      have hend : en = 8#usize := by simpa [r4] using he4
      subst st; subst en; rfl
  have hn4r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r4 =
      .ok (some (4#usize), r5) := by simpa [r4, ht5] using hn4
  obtain ⟨t6, hn5, ha5, he5⟩ := range_next_success r5 (by simp [r5])
  have ht6 : t6 = r6 := by
    cases t6 with
    | mk st en =>
      have hs : st = 6#usize := UScalar.eq_of_val_eq (by simpa [r5] using ha5)
      have hend : en = 8#usize := by simpa [r5] using he5
      subst st; subst en; rfl
  have hn5r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r5 =
      .ok (some (5#usize), r6) := by simpa [r5, ht6] using hn5
  obtain ⟨t7, hn6, ha6, he6⟩ := range_next_success r6 (by simp [r6])
  have ht7 : t7 = r7 := by
    cases t7 with
    | mk st en =>
      have hs : st = 7#usize := UScalar.eq_of_val_eq (by simpa [r6] using ha6)
      have hend : en = 8#usize := by simpa [r6] using he6
      subst st; subst en; rfl
  have hn6r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r6 =
      .ok (some (6#usize), r7) := by simpa [r6, ht7] using hn6
  obtain ⟨t8, hn7, ha7, he7⟩ := range_next_success r7 (by simp [r7])
  have ht8 : t8 = r8 := by
    cases t8 with
    | mk st en =>
      have hs : st = 8#usize := UScalar.eq_of_val_eq (by simpa [r7] using ha7)
      have hend : en = 8#usize := by simpa [r7] using he7
      subst st; subst en; rfl
  have hn7r : core.iter.range.IteratorRange.next core.iter.range.StepUsize r7 =
      .ok (some (7#usize), r8) := by simpa [r7, ht8] using hn7
  have hb0 : LimbBody ops sums r0 limbs =
      .ok (.cont (r1, l1)) := by
    exact old_limb_body_success_of_fold_segment ops sums r0 r1
      limbs l1 (0#usize) hn0r rfl h0
  have hb1 : LimbBody ops sums r1 l1 =
      .ok (.cont (r2, l2)) := by
    exact old_limb_body_success_of_fold_segment ops sums r1 r2
      l1 l2 (1#usize) hn1r rfl h1
  have hb2 : LimbBody ops sums r2 l2 =
      .ok (.cont (r3, l3)) := by
    exact old_limb_body_success_of_fold_segment ops sums r2 r3
      l2 l3 (2#usize) hn2r rfl h2
  have hb3 : LimbBody ops sums r3 l3 =
      .ok (.cont (r4, l4)) := by
    exact old_limb_body_success_of_fold_segment ops sums r3 r4
      l3 l4 (3#usize) hn3r rfl h3
  have hb4 : LimbBody ops sums r4 l4 =
      .ok (.cont (r5, l5)) := by
    exact old_limb_body_success_of_fold_segment ops sums r4 r5
      l4 l5 (4#usize) hn4r rfl h4
  have hb5 : LimbBody ops sums r5 l5 =
      .ok (.cont (r6, l6)) := by
    exact old_limb_body_success_of_fold_segment ops sums r5 r6
      l5 l6 (5#usize) hn5r rfl h5
  have hb6 : LimbBody ops sums r6 l6 =
      .ok (.cont (r7, l7)) := by
    exact old_limb_body_success_of_fold_segment ops sums r6 r7
      l6 l7 (6#usize) hn6r rfl h6
  have hb7 : LimbBody ops sums r7 l7 =
      .ok (.cont (r8, out)) := by
    exact old_limb_body_success_of_fold_segment ops sums r7 r8
      l7 out (7#usize) hn7r rfl h7
  have hdone : LimbBody ops sums r8 out = .ok (.done out) := by
    unfold LimbBody
    change (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r8
      match o with
      | none => ok (ControlFlow.done out)
      | some limb => do
        let x ← Array.index_usize sums limb
        let low ← lift (x &&& 2147483647#u64)
        let high ← x >>> 31#i32
        let part ← low + high
        let old ← Array.index_usize out limb
        let new ← old + part
        let updated ← Array.update out limb new
        ok (ControlFlow.cont (iter1, updated))) = .ok (.done out)
    have hn := range_next_none_success r8 (by simp [r8])
    rw [hn]
    rfl
  change Aeneas.Std.loop (limbStep ops sums)
    (r0, limbs) = .ok out
  exact loop_success_of_eight_steps (limbStep ops sums)
    (r0, limbs) (r1, l1) (r2, l2) (r3, l3) (r4, l4)
    (r5, l5) (r6, l6) (r7, l7) (r8, out) out hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hdone


/-- Success of the v6 fixed-call batch body transfers to the retained emitted
    batch body. The new eight-term body supplies the old term loop through the
    checked transfer, and its eight explicit fold/update groups reconstruct
    the actual old loop1 call. -/
theorem fixed_batch_body_success_old_body
    (ops : Ops) (q : Array Std.U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : AspisR1FastDotsBatchBodyAdvance.StepBy)
    (limbs limbs' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body
      ops q g slot iter limbs = .ok (.cont (iter', limbs'))) :
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      ops q g slot iter limbs = .ok (.cont (iter', limbs')) := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      simp only [bind_tc_ok] at hrest
      cases Result.ok.inj hrest
  | some start =>
      simp only [bind_tc_ok] at hrest
      obtain ⟨batchEnd, hadd, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨rangeEnd, hmin, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sums, hnewTerm, hrest⟩ := bind_success _ _ _ hrest
      let foldTail : Array U64 8#usize →
          Result (ControlFlow
            (AspisR1FastDotsBatchBodyAdvance.StepBy × Array U64 8#usize)
            (Array U64 8#usize)) := fun limbsOut =>
        .ok (.cont (iter1, limbsOut))
      have hfoldMap : (do
        let limbsOut ← foldEight sums limbs
        foldTail limbsOut) = .ok (.cont (iter', limbs')) := by
        unfold foldEight
        dsimp [foldTail]
        simp only [result_bind_assoc]
        exact hrest
      obtain ⟨limbsOut, hfold, hfinal⟩ := bind_success
        (foldEight sums limbs) foldTail (.cont (iter', limbs')) hfoldMap
      have hpair := ControlFlow.cont.inj (Result.ok.inj hfinal)
      have hiter : iter1 = iter' := congrArg Prod.fst hpair
      have hout : limbsOut = limbs' := congrArg Prod.snd hpair
      have holdTerm :
          AspisR1FastDotsNewTermLoopOldLoopTransferV1.OldLoop ops
            { start, «end» := rangeEnd } q g slot (Array.repeat 8#usize 0#u64) =
            .ok sums :=
        AspisR1FastDotsNewTermLoopOldLoopTransferV1.new_loop_success_old_loop
          ops q g slot { start := start, «end» := rangeEnd }
          (Array.repeat 8#usize 0#u64) sums hcount hnewTerm
      have holdLimb : LimbLoop ops { start := 0#usize, «end» := 8#usize }
          limbs sums = .ok limbsOut :=
        foldEight_success_old_limb_loop ops sums limbs limbsOut hfold
      change (do
        let (o, iter1) ← core.iter.adapters.step_by.IteratorStepBy.next
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
        match o with
        | none => ok (ControlFlow.done limbs)
        | some start => do
          let sums := Array.repeat 8#usize 0#u64
          let i ← start + 4#usize
          let i1 ← core.cmp.min core.cmp.OrdUsize i 26#usize
          let sums1 ← AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
            ops { start, «end» := i1 } q g slot sums
          let i2 ← ops.wideLimbCount
          let limbs1 ← AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
            ops { start := 0#usize, «end» := i2 } limbs sums1
          ok (ControlFlow.cont (iter1, limbs1))) =
          .ok (.cont (iter', limbs'))
      rw [hnext]
      simp only [bind_tc_ok, hadd, bind_tc_ok, hmin, bind_tc_ok,
        holdTerm, bind_tc_ok]
      rw [hcount]
      simp only [bind_tc_ok, holdLimb]
      rw [hiter, hout]

#print axioms fixed_batch_body_success_old_body

end AspisR1FastDotsNewOuterLimbLoopSegmentV1
