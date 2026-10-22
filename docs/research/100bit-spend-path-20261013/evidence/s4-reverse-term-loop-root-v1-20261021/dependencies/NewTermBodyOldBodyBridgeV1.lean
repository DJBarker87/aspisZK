import NewTermBodyLinearBoundV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsNewTermBodyOldBodyBridgeV1

abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := UScalar UScalarTy.U32
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsNewTermBodyLinearBoundV1.Ops
abbrev NewBody := AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody
abbrev OldBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body
abbrev OldInnerBody := AspisR1FastDotsFixedInnerBodyStepBridgeV1.OldInnerBody
abbrev OldInnerLoop := AspisR1FastDotsFixedInnerBodyStepBridgeV1.OldInnerLoop

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem identity_bind_success {α : Type} (m : Result α) (v : α)
    (h : (do let x ← m; ok x) = .ok v) : m = .ok v := by
  obtain ⟨x, hm, hk⟩ := bind_success m (fun x => ok x) v h
  exact hm.trans (congrArg Result.ok (Result.ok.inj hk))

private theorem emitted_segment_success {β : Type}
    (coefficient : Array U32 8#usize) (sums : Array U64 8#usize)
    (scalar : M31) (limb : Usize) (k : Array U64 8#usize → Result β) (out : β)
    (h : (do
      let c ← Array.index_usize coefficient limb
      let c64 ← lift (core.convert.num.FromU64U32.from c)
      let s64 ← lift (core.convert.num.FromU64U32.from scalar)
      let product ← c64 * s64
      let oldSum ← Array.index_usize sums limb
      let newSum ← oldSum + product
      let updated ← Array.update sums limb newSum
      k updated) = .ok out) :
    ∃ updated, AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient sums scalar limb = .ok updated ∧ k updated = .ok out := by
  obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ h
  obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨oldSum, holdSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨newSum, hnewSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨updated, hupdate, htail⟩ := bind_success _ _ _ hrest
  have hsegment : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
      coefficient sums scalar limb = .ok updated := by
    unfold AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
    simp only [hc, hc64, hs64, hproduct, holdSum, hnewSum, hupdate, bind_tc_ok]
  exact ⟨updated, hsegment, htail⟩

private theorem loop_success_of_eight_steps {α β : Type}
    (step : α → Result (ControlFlow α β))
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : α) (out : β)
    (h0 : step s0 = .ok (.cont s1)) (h1 : step s1 = .ok (.cont s2))
    (h2 : step s2 = .ok (.cont s3)) (h3 : step s3 = .ok (.cont s4))
    (h4 : step s4 = .ok (.cont s5)) (h5 : step s5 = .ok (.cont s6))
    (h6 : step s6 = .ok (.cont s7)) (h7 : step s7 = .ok (.cont s8))
    (hdone : step s8 = .ok (.done out)) :
    Aeneas.Std.loop step s0 = .ok out := by
  rw [Aeneas.Std.loop.eq_def, h0]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h1]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h2]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h3]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h4]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h5]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h6]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, h7]; simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def, hdone]

private theorem range_next_success (iter : Range)
    (hlt : iter.start.val < iter.end.val) :
    ∃ iter', core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') ∧ iter'.start.val = iter.start.val + 1 ∧
      iter'.end = iter.end := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
  have hltSpec : ∀ a b : Usize,
      core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  simp only [hlt, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hopt, hadvance⟩, hend⟩
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') := by rw [hrun, hopt]
  exact ⟨iter', hnext, hadvance, hend⟩

private theorem range_next_to_literal (iter iterNext : Range) (limb : Usize)
    (hstart : iter.start = limb) (hlt : iter.start.val < iter.end.val)
    (hnextStart : iterNext.start.val = iter.start.val + 1)
    (hend : iterNext.end = iter.end) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some limb, iterNext) := by
  obtain ⟨actual, hnext, hactualStart, hactualEnd⟩ := range_next_success iter hlt
  have hstartEq : actual.start = iterNext.start := by
    apply UScalar.eq_of_val_eq
    omega
  have hnextEq : actual = iterNext := by
    cases actual
    cases iterNext
    simp_all [hstartEq, hactualEnd, hend]
  rw [hnextEq, hstart] at hnext
  exact hnext

private theorem range_next_done (iter : Range) (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter hge)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hiter⟩
  cases hopt
  cases hiter
  exact hrun

private def innerStep (ops : Ops) (coefficient : Array U32 8#usize)
    (s : Range × Array U64 8#usize × M31) : Result (ControlFlow
      (Range × Array U64 8#usize × M31) (Array U64 8#usize)) :=
  OldInnerBody ops coefficient s.1 s.2.1 s.2.2

/-- For fixed-eight wrapped operations, success of the v6 explicit-coordinate
    term body also gives success of the retained old term-body declaration,
    with exactly the same range and sums. -/
theorem new_body_success_old_body
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hbody : NewBody ops q g slot iter sums = .ok (.cont (iter', sums'))) :
    OldBody ops q g slot iter sums = .ok (.cont (iter', sums')) := by
  unfold NewBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨i, hi, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i1, hi1, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i2, hi2, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i3, hi3, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i4, hi4, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨s, hs, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨r, hr, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨bytes, hbytes, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨parsed, hparse, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar, hunwrap, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨wide, hread, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coefficient, hcoeff, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sums1, h0, hrest⟩ := emitted_segment_success coefficient sums scalar 0#usize _ _ hrest
      obtain ⟨sums2, h1, hrest⟩ := emitted_segment_success coefficient sums1 scalar 1#usize _ _ hrest
      obtain ⟨sums3, h2, hrest⟩ := emitted_segment_success coefficient sums2 scalar 2#usize _ _ hrest
      obtain ⟨sums4, h3, hrest⟩ := emitted_segment_success coefficient sums3 scalar 3#usize _ _ hrest
      obtain ⟨sums5, h4, hrest⟩ := emitted_segment_success coefficient sums4 scalar 4#usize _ _ hrest
      obtain ⟨sums6, h5, hrest⟩ := emitted_segment_success coefficient sums5 scalar 5#usize _ _ hrest
      obtain ⟨sums7, h6, hrest⟩ := emitted_segment_success coefficient sums6 scalar 6#usize _ _ hrest
      obtain ⟨sums8, h7, hfinal⟩ := emitted_segment_success coefficient sums7 scalar 7#usize _ _ hrest
      have hpair : (iter1, sums8) = (iter', sums') := by
        exact ControlFlow.cont.inj (Result.ok.inj hfinal)
      have hiter : iter1 = iter' := congrArg Prod.fst hpair
      have hsums : sums8 = sums' := congrArg Prod.snd hpair
      have hi23 : i2 = i3 := Result.ok.inj (hi2.symm.trans hi3)
      have hi4' : (i2 + 4#usize : Result Usize) = .ok i4 := by
        simpa [hi23] using hi4
      have hn0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero =
          .ok (some 0#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_one) := by
        apply range_next_to_literal _ _ 0#usize (by rfl)
        · change (0#usize).val < (8#usize).val; scalar_tac
        · change (1#usize).val = (0#usize).val + 1; scalar_tac
        · rfl
      have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_one =
          .ok (some 1#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_two) := by
        apply range_next_to_literal _ _ 1#usize (by rfl)
        · change (1#usize).val < (8#usize).val; scalar_tac
        · change (2#usize).val = (1#usize).val + 1; scalar_tac
        · rfl
      have hn2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_two =
          .ok (some 2#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_three) := by
        apply range_next_to_literal _ _ 2#usize (by rfl)
        · change (2#usize).val < (8#usize).val; scalar_tac
        · change (3#usize).val = (2#usize).val + 1; scalar_tac
        · rfl
      have hn3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_three =
          .ok (some 3#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_four) := by
        apply range_next_to_literal _ _ 3#usize (by rfl)
        · change (3#usize).val < (8#usize).val; scalar_tac
        · change (4#usize).val = (3#usize).val + 1; scalar_tac
        · rfl
      have hn4 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_four =
          .ok (some 4#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_five) := by
        apply range_next_to_literal _ _ 4#usize (by rfl)
        · change (4#usize).val < (8#usize).val; scalar_tac
        · change (5#usize).val = (4#usize).val + 1; scalar_tac
        · rfl
      have hn5 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_five =
          .ok (some 5#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_six) := by
        apply range_next_to_literal _ _ 5#usize (by rfl)
        · change (5#usize).val < (8#usize).val; scalar_tac
        · change (6#usize).val = (5#usize).val + 1; scalar_tac
        · rfl
      have hn6 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_six =
          .ok (some 6#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_seven) := by
        apply range_next_to_literal _ _ 6#usize (by rfl)
        · change (6#usize).val < (8#usize).val; scalar_tac
        · change (7#usize).val = (6#usize).val + 1; scalar_tac
        · rfl
      have hn7 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_seven =
          .ok (some 7#usize, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight) := by
        apply range_next_to_literal _ _ 7#usize (by rfl)
        · change (7#usize).val < (8#usize).val; scalar_tac
        · change (8#usize).val = (7#usize).val + 1; scalar_tac
        · rfl
      have hb0 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums sums1 scalar 0#usize hn0 h0
      have hb1 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums1 sums2 scalar 1#usize hn1 h1
      have hb2 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums2 sums3 scalar 2#usize hn2 h2
      have hb3 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums3 sums4 scalar 3#usize hn3 h3
      have hb4 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums4 sums5 scalar 4#usize hn4 h4
      have hb5 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums5 sums6 scalar 5#usize hn5 h5
      have hb6 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums6 sums7 scalar 6#usize hn6 h6
      have hb7 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at_success_calls_old_inner_body
        ops coefficient _ _ sums7 sums8 scalar 7#usize hn7 h7
      have hnext8 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight =
          .ok (none, AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight) := by
        apply range_next_done
        change (8#usize).val ≥ (8#usize).val
        scalar_tac
      have hdone : OldInnerBody ops coefficient
          AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight sums8 scalar =
          .ok (.done sums8) := by
        change (do
          let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize
            AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight
          match o with
          | none => ok (ControlFlow.done sums8)
          | some limb => do
            let i ← Array.index_usize coefficient limb
            let i1 ← lift (core.convert.num.FromU64U32.from i)
            let i2 ← lift (core.convert.num.FromU64U32.from scalar)
            let i3 ← i1 * i2
            let i4 ← Array.index_usize sums8 limb
            let i5 ← i4 + i3
            let a ← Array.update sums8 limb i5
            ok (ControlFlow.cont (iter1, a, scalar))) = .ok (ControlFlow.done sums8)
        rw [hnext8]
        rfl
      have hloop : OldInnerLoop ops AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero
          sums scalar coefficient = .ok sums8 := by
        change Aeneas.Std.loop (innerStep ops coefficient)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero, sums, scalar) = .ok sums8
        exact loop_success_of_eight_steps (innerStep ops coefficient)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero, sums, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_one, sums1, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_two, sums2, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_three, sums3, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_four, sums4, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_five, sums5, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_six, sums6, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_seven, sums7, scalar)
          (AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_eight, sums8, scalar)
          sums8
          (by simpa [innerStep] using hb0) (by simpa [innerStep] using hb1)
          (by simpa [innerStep] using hb2) (by simpa [innerStep] using hb3)
          (by simpa [innerStep] using hb4) (by simpa [innerStep] using hb5)
          (by simpa [innerStep] using hb6) (by simpa [innerStep] using hb7)
          (by simpa [innerStep] using hdone)
      have hloop' : OldInnerLoop ops { start := 0#usize, «end» := 8#usize }
          sums scalar coefficient = .ok sums8 := by
        simpa [AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero] using hloop
      have hold : OldBody ops q g slot iter sums = .ok (.cont (iter', sums')) := by
        change (do
          let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
          match o with
          | none => ok (ControlFlow.done sums)
          | some term => do
            let i ← slot * 120#usize
            let i1 ← term * 4#usize
            let i2 ← i + i1
            let i3 ← i + i1
            let i4 ← i3 + 4#usize
            let s ← core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := i2, «end» := i4 }
            let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
            let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
            let o1 ← ops.m31FromBytes a
            let scalar ← core.option.Option.unwrap o1
            let we ← Array.index_usize g term
            let coefficient ← ops.wideToLimbs we
            let i5 ← ops.wideLimbCount
            let sums1 ← OldInnerLoop ops { start := 0#usize, «end» := i5 }
              sums scalar coefficient
            ok (ControlFlow.cont (iter1, sums1))) = .ok (ControlFlow.cont (iter', sums'))
        rw [hnext]
        simp only [bind_tc_ok, hi, hi1, hi2, hi4', hs, hr, hbytes,
          hparse, hunwrap, hread, hcoeff, hcount, hloop', bind_tc_ok]
        rw [hiter, hsums]
      simpa [hiter, hsums] using hold

#print axioms new_body_success_old_body

end AspisR1FastDotsNewTermBodyOldBodyBridgeV1
