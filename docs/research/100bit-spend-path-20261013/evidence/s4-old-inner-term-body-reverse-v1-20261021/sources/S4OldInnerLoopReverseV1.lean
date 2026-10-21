import FixedInnerBodyStepBridgeV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsOldInnerLoopReverseV1

abbrev Usize := Std.Usize
abbrev U32 := Std.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev M31 := AspisR1FastDotsFixedInnerBodyStepBridgeV1.M31
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsFixedInnerBodyStepBridgeV1.Ops
abbrev OldBody := AspisR1FastDotsFixedInnerBodyStepBridgeV1.OldInnerBody
abbrev OldLoop := AspisR1FastDotsFixedInnerBodyStepBridgeV1.OldInnerLoop
abbrev segment := AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem range_next_some (iter : Range) (hlt : iter.start.val < iter.end.val) :
    ∃ iter', core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') ∧ iter'.start.val = iter.start.val + 1 ∧
      iter'.end = iter.end := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
  have hltSpec : ∀ a b : Usize,
      core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by intros; rfl
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

private theorem range_next_none (iter : Range) (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
  have hltSpec : ∀ a b : Usize,
      core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  have hn : ¬ iter.start.val < iter.end.val := by omega
  simp only [hn, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hnone, hstart⟩, hend⟩
  have heq : iter' = iter := by
    cases iter with
    | mk a b => cases iter' with
      | mk c d => have hc : c = a := hstart; have hd : d = b := hend; subst c; subst d; rfl
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter) := by rw [hrun, hnone, heq]
  exact hnext

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok flow => cases flow with
    | done result =>
      simp only [hs, bind_tc_ok] at h
      have heq : result = out := Result.ok.inj h
      subst result
      exact Or.inl rfl
    | cont next =>
      simp only [hs, bind_tc_ok] at h
      exact Or.inr ⟨next, rfl, h⟩

inductive SegmentTrace (coeff : Array U32 8#usize) (scalar : M31) :
    Range → Array U64 8#usize → Array U64 8#usize → Type where
  | step {iter iter' : Range} {initial mid final : Array U64 8#usize}
      (hlt : iter.start.val < iter.end.val)
      (hstart : iter'.start.val = iter.start.val + 1)
      (hend : iter'.end = iter.end)
      (hsegment : segment coeff initial scalar iter.start = .ok mid)
      (tail : SegmentTrace coeff scalar iter' mid final) :
      SegmentTrace coeff scalar iter initial final
  | finish {iter : Range} {initial final : Array U64 8#usize}
      (hge : iter.start.val ≥ iter.end.val) (heq : final = initial) :
      SegmentTrace coeff scalar iter initial final

private def innerStep (ops : Ops) (coeff : Array U32 8#usize) (scalar : M31) :
    (Range × Array U64 8#usize × M31) →
      Result (ControlFlow (Range × Array U64 8#usize × M31) (Array U64 8#usize)) :=
  fun s => OldBody ops coeff s.1 s.2.1 s.2.2

private theorem body_continue_segment (ops : Ops) (coeff : Array U32 8#usize)
    (scalar : M31) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : OldBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar))) :
    ∃ limb, limb = iter.start ∧ iter.start.val < iter.end.val ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some limb, iter') ∧ iter'.start.val = iter.start.val + 1 ∧
      iter'.end = iter.end ∧ segment coeff sums scalar limb = .ok sums' := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (ControlFlow.done sums)
    | some limb => do
      let i ← Array.index_usize coeff limb
      let i1 ← lift (core.convert.num.FromU64U32.from i)
      let i2 ← lift (core.convert.num.FromU64U32.from scalar)
      let i3 ← i1 * i2
      let i4 ← Array.index_usize sums limb
      let i5 ← i4 + i3
      let a ← Array.update sums limb i5
      ok (ControlFlow.cont (iter1, a, scalar))) =
      .ok (ControlFlow.cont (iter', sums', scalar)) at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases pair with ⟨option, iter1⟩
  cases option with
  | none => cases Result.ok.inj hrest
  | some limb =>
    obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨oldSum, hold, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨newSum, hadd, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨updated, hupdate, hrest⟩ := bind_success _ _ _ hrest
    have htuple := ControlFlow.cont.inj (Result.ok.inj hrest)
    have hiter : iter1 = iter' := congrArg Prod.fst htuple
    have htailPair : (updated, scalar) = (sums', scalar) := congrArg Prod.snd htuple
    have hsums : updated = sums' := congrArg Prod.fst htailPair
    have hseg : segment coeff sums scalar limb = .ok updated := by
      unfold segment AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
      simp only [hc, hc64, hs64, hproduct, hold, hadd, hupdate, bind_tc_ok]
    have hlt : iter.start.val < iter.end.val := by
      by_contra hnot
      have hnone := range_next_none iter (by omega)
      rw [hnext] at hnone
      cases Result.ok.inj hnone
    rcases range_next_some iter hlt with ⟨actual, hactual, hadv, hend⟩
    have hnext' : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some limb, iter') := by rw [hiter] at hnext; exact hnext
    have heq := Result.ok.inj (hnext'.symm.trans hactual)
    rcases Prod.mk.inj heq with ⟨hopt, hit⟩
    have hlimb : limb = iter.start := Option.some.inj hopt
    have hactualEq : actual = iter' := hit.symm
    have hadv' : iter'.start.val = iter.start.val + 1 := by
      rw [← hactualEq]
      exact hadv
    have hend' : iter'.end = iter.end := by
      rw [← hactualEq]
      exact hend
    subst limb
    have hout : updated = sums' := by simpa using hsums
    subst updated
    exact ⟨iter.start, rfl, hlt, hnext', hadv', hend', hseg⟩

private theorem body_done_identity (ops : Ops) (coeff : Array U32 8#usize)
    (scalar : M31) (iter : Range) (sums out : Array U64 8#usize)
    (hbody : OldBody ops coeff iter sums scalar = .ok (.done out)) :
    iter.start.val ≥ iter.end.val ∧ out = sums := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (ControlFlow.done sums)
    | some limb => do
      let i ← Array.index_usize coeff limb
      let i1 ← lift (core.convert.num.FromU64U32.from i)
      let i2 ← lift (core.convert.num.FromU64U32.from scalar)
      let i3 ← i1 * i2
      let i4 ← Array.index_usize sums limb
      let i5 ← i4 + i3
      let a ← Array.update sums limb i5
      ok (ControlFlow.cont (iter1, a, scalar))) = .ok (ControlFlow.done out) at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases pair with ⟨option, _⟩
  cases option with
  | none =>
      have hout : out = sums := (ControlFlow.done.inj (Result.ok.inj hrest)).symm
      have hge : iter.start.val ≥ iter.end.val := by
        by_contra hn
        have hlt : iter.start.val < iter.end.val := by omega
        obtain ⟨next, hsome, _, _⟩ := range_next_some iter hlt
        rw [hnext] at hsome
        cases Result.ok.inj hsome
      exact ⟨hge, hout⟩
  | some _ =>
    repeat' (first | obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest)
    cases Result.ok.inj hrest

theorem old_inner_loop_success_trace (ops : Ops) (coeff : Array U32 8#usize)
    (scalar : M31) (iter : Range) (sums out : Array U64 8#usize)
    (hbound : iter.start.val ≤ iter.end.val)
    (hloop : OldLoop ops iter sums scalar coeff = .ok out) :
    Nonempty (SegmentTrace coeff scalar iter sums out) := by
  let step := innerStep ops coeff scalar
  change Aeneas.Std.loop step (iter, sums, scalar) = .ok out at hloop
  induction hmeasure : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums with
  | h n ih =>
    rcases loop_success_cases step (iter, sums, scalar) out hloop with hdone | ⟨state', hcont, htail⟩
    · have hbody : OldBody ops coeff iter sums scalar = .ok (.done out) := by
        simpa only [step, innerStep] using hdone
      have hout := body_done_identity ops coeff scalar iter sums out hbody
      exact ⟨SegmentTrace.finish hout.1 hout.2⟩
    · rcases state' with ⟨iter', sums', scalar'⟩
      have hstep : OldBody ops coeff iter sums scalar =
          .ok (.cont (iter', sums', scalar')) := by
        simpa only [step, innerStep] using hcont
      have hscalar' : scalar' = scalar := by
          have hs := hstep
          unfold OldBody at hs
          change (do
            let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
            match o with
            | none => ok (ControlFlow.done sums)
            | some limb => do
              let i ← Array.index_usize coeff limb
              let i1 ← lift (core.convert.num.FromU64U32.from i)
              let i2 ← lift (core.convert.num.FromU64U32.from scalar)
              let i3 ← i1 * i2
              let i4 ← Array.index_usize sums limb
              let i5 ← i4 + i3
              let a ← Array.update sums limb i5
              ok (ControlFlow.cont (iter1, a, scalar))) =
              .ok (ControlFlow.cont (iter', sums', scalar')) at hs
          obtain ⟨pair, _, hs⟩ := bind_success _ _ _ hs
          rcases pair with ⟨option, _⟩
          cases option with
          | none => cases Result.ok.inj hs
          | some _ =>
              repeat' (first | obtain ⟨_, _, hs⟩ := bind_success _ _ _ hs)
              have htuple := ControlFlow.cont.inj (Result.ok.inj hs)
              exact (congrArg Prod.snd (congrArg Prod.snd htuple)).symm
      have hbody : OldBody ops coeff iter sums scalar =
          .ok (ControlFlow.cont (iter', sums', scalar)) := by
        simpa [hscalar'] using hstep
      obtain ⟨limb, hlimb, hlt, _hnext, hadvance, hend, hsegment⟩ :=
        body_continue_segment ops coeff scalar iter iter' sums sums' hbody
      rw [hlimb] at hsegment
      have hn : iter.end.val - iter.start.val = n := hmeasure
      have hbound' : iter'.start.val ≤ iter'.end.val := by rw [hadvance, hend]; omega
      have hdec : iter'.end.val - iter'.start.val < n := by rw [hadvance, hend]; omega
      subst scalar'
      obtain ⟨tail⟩ := ih _ hdec iter' sums' hbound' htail rfl
      exact ⟨SegmentTrace.step hlt hadvance hend hsegment tail⟩

private def seg8 (coeff : Array U32 8#usize) (scalar : M31)
    (sums limbs : Array U64 8#usize) (limb : Usize) : Result (Array U64 8#usize) :=
  segment coeff limbs scalar limb

private theorem range_eq_components_inner (iter : Range) (start stop : Usize)
    (hs : iter.start.val = start.val) (he : iter.end.val = stop.val) :
    iter = { start := start, «end» := stop } := by
  cases iter with
  | mk actualStart actualEnd =>
    have hs' : actualStart = start := UScalar.eq_of_val_eq hs
    have he' : actualEnd = stop := UScalar.eq_of_val_eq he
    subst actualStart
    subst actualEnd
    rfl
theorem trace_eight_segment_successes
    (coeff : Array U32 8#usize) (scalar : M31)
    (sums initial out : Array U64 8#usize)
    (trace : SegmentTrace coeff scalar { start := 0#usize, «end» := 8#usize } initial out) :
    ∃ l1 l2 l3 l4 l5 l6 l7,
      seg8 coeff scalar sums initial 0#usize = .ok l1 ∧
      seg8 coeff scalar sums l1 1#usize = .ok l2 ∧
      seg8 coeff scalar sums l2 2#usize = .ok l3 ∧
      seg8 coeff scalar sums l3 3#usize = .ok l4 ∧
      seg8 coeff scalar sums l4 4#usize = .ok l5 ∧
      seg8 coeff scalar sums l5 5#usize = .ok l6 ∧
      seg8 coeff scalar sums l6 6#usize = .ok l7 ∧
      seg8 coeff scalar sums l7 7#usize = .ok out := by
  let r0 : Range := { start := 0#usize, «end» := 8#usize }
  let r1 : Range := { start := 1#usize, «end» := 8#usize }
  let r2 : Range := { start := 2#usize, «end» := 8#usize }
  let r3 : Range := { start := 3#usize, «end» := 8#usize }
  let r4 : Range := { start := 4#usize, «end» := 8#usize }
  let r5 : Range := { start := 5#usize, «end» := 8#usize }
  let r6 : Range := { start := 6#usize, «end» := 8#usize }
  let r7 : Range := { start := 7#usize, «end» := 8#usize }
  let r8 : Range := { start := 8#usize, «end» := 8#usize }
  change SegmentTrace coeff scalar r0 initial out at trace
  cases trace with
  | finish hge heq =>
      have hfalse : ¬ (0#usize).val ≥ (8#usize).val := by scalar_tac
      exact False.elim (hfalse (by simpa [r0] using hge))
  | @step it0 itN0 st0 mid0 fin0 hlt0 hs0 he0 hf0 tail0 =>
      let l1 := mid0
      have hseg0 : seg8 coeff scalar sums initial 0#usize = .ok l1 := by
        change seg8 coeff scalar sums initial 0#usize = .ok mid0 at hf0
        exact hf0
      have hnextStart0 : itN0.start.val = (1#usize).val := by
        have hv := hs0
        have hsimp : itN0.start.val = (0#usize).val + 1 := by simpa [r0] using hv
        scalar_tac
      have hnextEnd0 : itN0.end.val = (8#usize).val := by
        rw [he0]
      have hrange1 : itN0 = r1 := by
        exact range_eq_components_inner itN0 (1#usize) (8#usize) hnextStart0 hnextEnd0
      subst itN0
      cases tail0 with
        | finish hge heq =>
            have hfalse : ¬ (1#usize).val ≥ (8#usize).val := by scalar_tac
            exact False.elim (hfalse (by simpa [r1] using hge))
        | @step it1 itN1 st1 mid1 fin1 hlt1 hs1 he1 hf1 tail1 =>
          let l2 := mid1
          have hseg1 : seg8 coeff scalar sums l1 1#usize = .ok l2 := by
            change seg8 coeff scalar sums l1 1#usize = .ok mid1 at hf1
            exact hf1
          have hnextStart1 : itN1.start.val = (2#usize).val := by
            have hv := hs1
            have hsimp : itN1.start.val = (1#usize).val + 1 := by simpa [r1] using hv
            scalar_tac
          have hnextEnd1 : itN1.end.val = (8#usize).val := by
            rw [he1]
          have hrange2 : itN1 = r2 := by
            exact range_eq_components_inner itN1 (2#usize) (8#usize) hnextStart1 hnextEnd1
          subst itN1
          cases tail1 with
            | finish hge heq =>
                have hfalse : ¬ (2#usize).val ≥ (8#usize).val := by scalar_tac
                exact False.elim (hfalse (by simpa [r2] using hge))
            | @step it2 itN2 st2 mid2 fin2 hlt2 hs2 he2 hf2 tail2 =>
              let l3 := mid2
              have hseg2 : seg8 coeff scalar sums l2 2#usize = .ok l3 := by
                change seg8 coeff scalar sums l2 2#usize = .ok mid2 at hf2
                exact hf2
              have hnextStart2 : itN2.start.val = (3#usize).val := by
                have hv := hs2
                have hsimp : itN2.start.val = (2#usize).val + 1 := by simpa [r2] using hv
                scalar_tac
              have hnextEnd2 : itN2.end.val = (8#usize).val := by
                rw [he2]
              have hrange3 : itN2 = r3 := by
                exact range_eq_components_inner itN2 (3#usize) (8#usize) hnextStart2 hnextEnd2
              subst itN2
              cases tail2 with
                | finish hge heq =>
                    have hfalse : ¬ (3#usize).val ≥ (8#usize).val := by scalar_tac
                    exact False.elim (hfalse (by simpa [r3] using hge))
                | @step it3 itN3 st3 mid3 fin3 hlt3 hs3 he3 hf3 tail3 =>
                  let l4 := mid3
                  have hseg3 : seg8 coeff scalar sums l3 3#usize = .ok l4 := by
                    change seg8 coeff scalar sums l3 3#usize = .ok mid3 at hf3
                    exact hf3
                  have hnextStart3 : itN3.start.val = (4#usize).val := by
                    have hv := hs3
                    have hsimp : itN3.start.val = (3#usize).val + 1 := by simpa [r3] using hv
                    scalar_tac
                  have hnextEnd3 : itN3.end.val = (8#usize).val := by
                    rw [he3]
                  have hrange4 : itN3 = r4 := by
                    exact range_eq_components_inner itN3 (4#usize) (8#usize) hnextStart3 hnextEnd3
                  subst itN3
                  cases tail3 with
                    | finish hge heq =>
                        have hfalse : ¬ (4#usize).val ≥ (8#usize).val := by scalar_tac
                        exact False.elim (hfalse (by simpa [r4] using hge))
                    | @step it4 itN4 st4 mid4 fin4 hlt4 hs4 he4 hf4 tail4 =>
                      let l5 := mid4
                      have hseg4 : seg8 coeff scalar sums l4 4#usize = .ok l5 := by
                        change seg8 coeff scalar sums l4 4#usize = .ok mid4 at hf4
                        exact hf4
                      have hnextStart4 : itN4.start.val = (5#usize).val := by
                        have hv := hs4
                        have hsimp : itN4.start.val = (4#usize).val + 1 := by simpa [r4] using hv
                        scalar_tac
                      have hnextEnd4 : itN4.end.val = (8#usize).val := by
                        rw [he4]
                      have hrange5 : itN4 = r5 := by
                        exact range_eq_components_inner itN4 (5#usize) (8#usize) hnextStart4 hnextEnd4
                      subst itN4
                      cases tail4 with
                        | finish hge heq =>
                            have hfalse : ¬ (5#usize).val ≥ (8#usize).val := by scalar_tac
                            exact False.elim (hfalse (by simpa [r5] using hge))
                        | @step it5 itN5 st5 mid5 fin5 hlt5 hs5 he5 hf5 tail5 =>
                          let l6 := mid5
                          have hseg5 : seg8 coeff scalar sums l5 5#usize = .ok l6 := by
                            change seg8 coeff scalar sums l5 5#usize = .ok mid5 at hf5
                            exact hf5
                          have hnextStart5 : itN5.start.val = (6#usize).val := by
                            have hv := hs5
                            have hsimp : itN5.start.val = (5#usize).val + 1 := by simpa [r5] using hv
                            scalar_tac
                          have hnextEnd5 : itN5.end.val = (8#usize).val := by
                            rw [he5]
                          have hrange6 : itN5 = r6 := by
                            exact range_eq_components_inner itN5 (6#usize) (8#usize) hnextStart5 hnextEnd5
                          subst itN5
                          cases tail5 with
                            | finish hge heq =>
                                have hfalse : ¬ (6#usize).val ≥ (8#usize).val := by scalar_tac
                                exact False.elim (hfalse (by simpa [r6] using hge))
                            | @step it6 itN6 st6 mid6 fin6 hlt6 hs6 he6 hf6 tail6 =>
                              let l7 := mid6
                              have hseg6 : seg8 coeff scalar sums l6 6#usize = .ok l7 := by
                                change seg8 coeff scalar sums l6 6#usize = .ok mid6 at hf6
                                exact hf6
                              have hnextStart6 : itN6.start.val = (7#usize).val := by
                                have hv := hs6
                                have hsimp : itN6.start.val = (6#usize).val + 1 := by simpa [r6] using hv
                                scalar_tac
                              have hnextEnd6 : itN6.end.val = (8#usize).val := by
                                rw [he6]
                              have hrange7 : itN6 = r7 := by
                                exact range_eq_components_inner itN6 (7#usize) (8#usize) hnextStart6 hnextEnd6
                              subst itN6
                              cases tail6 with
                                | finish hge heq =>
                                    have hfalse : ¬ (7#usize).val ≥ (8#usize).val := by scalar_tac
                                    exact False.elim (hfalse (by simpa [r7] using hge))
                                | @step it7 itN7 st7 mid7 fin7 hlt7 hs7 he7 hf7 tail7 =>
                                  let l8 := mid7
                                  have hseg7 : seg8 coeff scalar sums l7 7#usize = .ok l8 := by
                                    change seg8 coeff scalar sums l7 7#usize = .ok mid7 at hf7
                                    exact hf7
                                  have hnextStart7 : itN7.start.val = (8#usize).val := by
                                    have hv := hs7
                                    have hsimp : itN7.start.val = (7#usize).val + 1 := by simpa [r7] using hv
                                    scalar_tac
                                  have hnextEnd7 : itN7.end.val = (8#usize).val := by
                                    rw [he7]
                                  have hrange8 : itN7 = r8 := by
                                    exact range_eq_components_inner itN7 (8#usize) (8#usize) hnextStart7 hnextEnd7
                                  subst itN7
                                  cases tail7 with
                                    | finish hge heq =>
                                        have hlast : seg8 coeff scalar sums l7 7#usize = .ok out := by
                                          have hout : out = mid7 := heq
                                          simpa [l8, hout] using hseg7
                                        exact ⟨l1,l2,l3,l4,l5,l6,l7,hseg0,hseg1,hseg2,hseg3,hseg4,hseg5,hseg6,hlast⟩
                                    | @step _ _ _ _ _ hlt8 _ _ _ _ =>
                                        have hbad : (8#usize).val < (8#usize).val := by
                                          simpa [hnextStart7, hnextEnd7] using hlt8
                                        omega


#print axioms body_continue_segment
#print axioms old_inner_loop_success_trace
end AspisR1FastDotsOldInnerLoopReverseV1
