import Aeneas
import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1FastDotsCurrent.FunsOpsFixedV6
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsFixedInnerBodyStepBridgeV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Std.Usize
abbrev U32 := Std.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev Range := core.ops.range.Range Usize
abbrev OldInnerBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body
abbrev OldInnerLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0
abbrev NewTermBody := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0.body

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem identity_bind_success {α : Type} (m : Result α) (v : α)
    (h : (do let x ← m; ok x) = ok v) : m = ok v := by
  obtain ⟨x, hm, hk⟩ := bind_success m (fun x => ok x) v h
  exact hm.trans (congrArg Result.ok (Result.ok.inj hk))

abbrev explicit_segment_at (coefficient : Array U32 8#usize)
    (sums : Array U64 8#usize) (scalar : M31) (limb : Usize) :
    Result (Array U64 8#usize) := do
  let i5 ← Array.index_usize coefficient limb
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 ← lift (core.convert.num.FromU64U32.from scalar)
  let i8 ← i6 * i7
  let i9 ← Array.index_usize sums limb
  let i10 ← i9 + i8
  Array.update sums limb i10

abbrev explicit_segment_zero (coefficient : Array U32 8#usize)
    (sums : Array U64 8#usize) (scalar : M31) : Result (Array U64 8#usize) :=
  explicit_segment_at coefficient sums scalar 0#usize

private theorem range_next_success (iter : Range)
    (hlt : iter.start.val < iter.end.val) :
    ∃ iter',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter') ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
    intro x
    rfl
  have hltSpec : ∀ a b : Usize,
      core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by
    intros
    rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  simp only [hlt, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hopt, hadvance⟩, hend⟩
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') := by
    rw [hrun, hopt]
  exact ⟨iter', hnext, hadvance, hend⟩

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
    ∃ updated, explicit_segment_at coefficient sums scalar limb = .ok updated ∧
      k updated = .ok out := by
  obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ h
  obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨oldSum, holdSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨newSum, hnewSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨updated, hupdate, htail⟩ := bind_success _ _ _ hrest
  have hsegment : explicit_segment_at coefficient sums scalar limb = .ok updated := by
    unfold explicit_segment_at
    simp only [hc, hc64, hs64, hproduct, holdSum, hnewSum, hupdate, bind_tc_ok]
  exact ⟨updated, hsegment, htail⟩

theorem one_coordinate_calls_old_inner_body
    (ops : Ops) (coeff : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize) (scalar : M31) (limb : Usize)
    (c : U32) (c64 s64 product oldSum newSum : U64)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some limb, iter'))
    (hcoeff : Array.index_usize coeff limb = .ok c)
    (hfromc : lift (core.convert.num.FromU64U32.from c) = .ok c64)
    (hfroms : lift (core.convert.num.FromU64U32.from scalar) = .ok s64)
    (hmul : (do let p ← (c64 * s64 : Result U64); ok p) = .ok product)
    (hsum : Array.index_usize sums limb = .ok oldSum)
    (hadd : (do let s ← (oldSum + product : Result U64); ok s) = .ok newSum)
    (hupdate : Array.update sums limb newSum = .ok sums') :
    OldInnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar)) := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (done sums)
    | some limb => do
      let i ← Array.index_usize coeff limb
      let i1 ← lift (core.convert.num.FromU64U32.from i)
      let i2 ← lift (core.convert.num.FromU64U32.from scalar)
      let i3 ← i1 * i2
      let i4 ← Array.index_usize sums limb
      let i5 ← i4 + i3
      let a ← Array.update sums limb i5
      ok (cont (iter1, a, scalar))) = .ok (.cont (iter', sums', scalar))
  rw [hnext]
  have hmul' : (c64 * s64 : Result U64) = .ok product := identity_bind_success (c64 * s64) product hmul
  have hadd' : (oldSum + product : Result U64) = .ok newSum := identity_bind_success (oldSum + product) newSum hadd
  simp only [bind_tc_ok, hcoeff, hfromc, hfroms, bind_tc_ok, hmul', hsum, bind_tc_ok, hadd', hupdate]

theorem explicit_segment_zero_success_calls_old_inner_body
    (ops : Ops) (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize) (scalar : M31)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some 0#usize, iter'))
    (hsegment : explicit_segment_zero coefficient sums scalar = .ok sums') :
    OldInnerBody ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar)) := by
  unfold explicit_segment_zero at hsegment
  obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ hsegment
  obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨oldSum, holdSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨newSum, hnewSum, hrest⟩ := bind_success _ _ _ hrest
  have hresult : Array.update sums 0#usize newSum = .ok sums' := by
    exact hrest
  have hmul : (do let p ← (c64 * s64 : Result U64); ok p) = .ok product := by
    simp only [hproduct, bind_tc_ok]
  have hadd : (do let s ← (oldSum + product : Result U64); ok s) = .ok newSum := by
    simp only [hnewSum, bind_tc_ok]
  exact one_coordinate_calls_old_inner_body ops coefficient iter iter' sums sums' scalar
    0#usize c c64 s64 product oldSum newSum hnext hc hc64 hs64 hmul holdSum hadd hresult

theorem explicit_segment_at_success_calls_old_inner_body
    (ops : Ops) (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize) (scalar : M31) (limb : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some limb, iter'))
    (hsegment : explicit_segment_at coefficient sums scalar limb = .ok sums') :
    OldInnerBody ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar)) := by
  unfold explicit_segment_at at hsegment
  obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ hsegment
  obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨oldSum, holdSum, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨newSum, hnewSum, hrest⟩ := bind_success _ _ _ hrest
  have hupdate : Array.update sums limb newSum = .ok sums' := hrest
  have hmul : (do let p ← (c64 * s64 : Result U64); ok p) = .ok product := by
    simp only [hproduct, bind_tc_ok]
  have hadd : (do let s ← (oldSum + product : Result U64); ok s) = .ok newSum := by
    simp only [hnewSum, bind_tc_ok]
  exact one_coordinate_calls_old_inner_body ops coefficient iter iter' sums sums' scalar
    limb c c64 s64 product oldSum newSum hnext hc hc64 hs64 hmul holdSum hadd hupdate

theorem new_term_body_success_exposes_first_segment
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : NewTermBody ops q g slot iter sums = .ok (.cont (iter', sums'))) :
    ∃ coefficient : Array U32 8#usize, ∃ scalar : M31, ∃ sums1 : Array U64 8#usize,
        explicit_segment_at coefficient sums scalar 0#usize = .ok sums1 := by
  unfold NewTermBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar, hunwrapOption, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨wide, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coefficient, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨c, hc, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨c64, hc64, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨s64, hs64, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨product, hproduct, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨oldSum, holdSum, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨newSum, hnewSum, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sums1, hupdate, _⟩ := bind_success _ _ _ hrest
      have hsegment : explicit_segment_at coefficient sums scalar 0#usize = .ok sums1 := by
        unfold explicit_segment_at
        simp only [hc, hc64, hs64, hproduct, holdSum, hnewSum, hupdate,
          bind_tc_ok]
      exact ⟨coefficient, scalar, sums1, hsegment⟩

def limb_range_zero : Range := { start := 0#usize, «end» := 8#usize }
def limb_range_one : Range := { start := 1#usize, «end» := 8#usize }
def limb_range_two : Range := { start := 2#usize, «end» := 8#usize }
def limb_range_three : Range := { start := 3#usize, «end» := 8#usize }
def limb_range_four : Range := { start := 4#usize, «end» := 8#usize }
def limb_range_five : Range := { start := 5#usize, «end» := 8#usize }
def limb_range_six : Range := { start := 6#usize, «end» := 8#usize }
def limb_range_seven : Range := { start := 7#usize, «end» := 8#usize }
def limb_range_eight : Range := { start := 8#usize, «end» := 8#usize }

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

private def oldInnerStep (ops : Ops) (coefficient : Array U32 8#usize)
    (s : Range × Array U64 8#usize × M31) : Result (ControlFlow
      (Range × Array U64 8#usize × M31) (Array U64 8#usize)) :=
  OldInnerBody ops coefficient s.1 s.2.1 s.2.2

theorem new_term_body_success_runs_old_inner_body_first
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (outerIter outerIter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : NewTermBody ops q g slot outerIter sums = .ok (.cont (outerIter', sums'))) :
    ∃ coefficient : Array U32 8#usize, ∃ scalar : M31,
      ∃ sums1 : Array U64 8#usize, ∃ limbIter1 : Range,
        explicit_segment_at coefficient sums scalar 0#usize = .ok sums1 ∧
        OldInnerBody ops coefficient limb_range_zero sums scalar =
          .ok (.cont (limbIter1, sums1, scalar)) := by
  obtain ⟨coefficient, scalar, sums1, hsegment⟩ :=
    new_term_body_success_exposes_first_segment ops q g slot outerIter outerIter' sums sums' hbody
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
    intro x
    rfl
  have hltSpec : ∀ a b : Usize,
      core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by
    intros
    rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    hclone hltSpec limb_range_zero
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, limbIter1⟩
  have hlt : limb_range_zero.start.val < limb_range_zero.end.val := by
    decide
  simp only [hlt, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hopt, _hadvance⟩, _hend⟩
  have hopt' : o = some 0#usize := by
    simpa [limb_range_zero] using hopt
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_zero =
      .ok (some 0#usize, limbIter1) := by
    rw [hrun, hopt']
  have hinner := explicit_segment_zero_success_calls_old_inner_body
    ops coefficient limb_range_zero limbIter1 sums sums1 scalar hnext hsegment
  exact ⟨coefficient, scalar, sums1, limbIter1, hsegment, hinner⟩

theorem new_term_body_success_exposes_eight_segments
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : NewTermBody ops q g slot iter sums = .ok (.cont (iter', sums'))) :
    ∃ term : Usize, ∃ bytes : Array U8 4#usize,
      ∃ wide : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact,
      ∃ coefficient : Array U32 8#usize, ∃ scalar : M31,
      ∃ sums1 sums2 sums3 sums4 sums5 sums6 sums7 sums8 : Array U64 8#usize,
        Array.index_usize g term = .ok wide ∧
        ops.wideToLimbs wide = .ok coefficient ∧
        ops.m31FromBytes bytes = .ok (some scalar) ∧
        explicit_segment_at coefficient sums scalar 0#usize = .ok sums1 ∧
        explicit_segment_at coefficient sums1 scalar 1#usize = .ok sums2 ∧
        explicit_segment_at coefficient sums2 scalar 2#usize = .ok sums3 ∧
        explicit_segment_at coefficient sums3 scalar 3#usize = .ok sums4 ∧
        explicit_segment_at coefficient sums4 scalar 4#usize = .ok sums5 ∧
        explicit_segment_at coefficient sums5 scalar 5#usize = .ok sums6 ∧
        explicit_segment_at coefficient sums6 scalar 6#usize = .ok sums7 ∧
        explicit_segment_at coefficient sums7 scalar 7#usize = .ok sums8 ∧
        sums8 = sums' := by
  unfold NewTermBody at hbody
  obtain ⟨⟨o, _iter1⟩, _hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨bytes, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨parsed, hparse, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar, hunwrapOption, hrest⟩ := bind_success _ _ _ hrest
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
      have hpair : (iter', sums') = (_iter1, sums8) := by
        exact (ControlFlow.cont.inj (Result.ok.inj hfinal)).symm
      have hparsedEq : parsed = some scalar := by
        cases parsed with
        | none => simp [core.option.Option.unwrap] at hunwrapOption
        | some value =>
            simp [core.option.Option.unwrap] at hunwrapOption
            subst scalar
            rfl
      exact ⟨term, bytes, wide, coefficient, scalar, sums1, sums2, sums3, sums4,
        sums5, sums6, sums7, sums8, hread, hcoeff, (by simpa only [hparsedEq] using hparse), h0, h1, h2, h3, h4,
        h5, h6, h7, (congrArg Prod.snd hpair).symm⟩

theorem new_term_body_success_supplies_old_inner_loop
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (outerIter outerIter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : NewTermBody ops q g slot outerIter sums = .ok (.cont (outerIter', sums'))) :
    ∃ term : Usize, ∃ bytes : Array U8 4#usize,
      ∃ wide : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact,
      ∃ coefficient : Array U32 8#usize, ∃ scalar : M31,
      ∃ sums1 sums2 sums3 sums4 sums5 sums6 sums7 sums8 : Array U64 8#usize,
        Array.index_usize g term = .ok wide ∧
        ops.wideToLimbs wide = .ok coefficient ∧
        ops.m31FromBytes bytes = .ok (some scalar) ∧
        explicit_segment_at coefficient sums scalar 0#usize = .ok sums1 ∧
        explicit_segment_at coefficient sums1 scalar 1#usize = .ok sums2 ∧
        explicit_segment_at coefficient sums2 scalar 2#usize = .ok sums3 ∧
        explicit_segment_at coefficient sums3 scalar 3#usize = .ok sums4 ∧
        explicit_segment_at coefficient sums4 scalar 4#usize = .ok sums5 ∧
        explicit_segment_at coefficient sums5 scalar 5#usize = .ok sums6 ∧
        explicit_segment_at coefficient sums6 scalar 6#usize = .ok sums7 ∧
        explicit_segment_at coefficient sums7 scalar 7#usize = .ok sums8 ∧
        sums8 = sums' ∧
        OldInnerLoop ops limb_range_zero sums scalar coefficient = .ok sums' := by
  obtain ⟨term, bytes, wide, coefficient, scalar, sums1, sums2, sums3, sums4,
      sums5, sums6, sums7, sums8, hread, hcoeff, hparse, h0, h1, h2, h3,
      h4, h5, h6, h7, hfinal⟩ :=
    new_term_body_success_exposes_eight_segments ops q g slot outerIter outerIter' sums sums' hbody
  have hn0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_zero =
      .ok (some 0#usize, limb_range_one) := by
    apply range_next_to_literal limb_range_zero limb_range_one 0#usize (by rfl)
    · change (0#usize).val < (8#usize).val
      scalar_tac
    · change (1#usize).val = (0#usize).val + 1
      scalar_tac
    · rfl
  have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_one =
      .ok (some 1#usize, limb_range_two) := by
    apply range_next_to_literal limb_range_one limb_range_two 1#usize (by rfl)
    · change (1#usize).val < (8#usize).val
      scalar_tac
    · change (2#usize).val = (1#usize).val + 1
      scalar_tac
    · rfl
  have hn2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_two =
      .ok (some 2#usize, limb_range_three) := by
    apply range_next_to_literal limb_range_two limb_range_three 2#usize (by rfl)
    · change (2#usize).val < (8#usize).val
      scalar_tac
    · change (3#usize).val = (2#usize).val + 1
      scalar_tac
    · rfl
  have hn3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_three =
      .ok (some 3#usize, limb_range_four) := by
    apply range_next_to_literal limb_range_three limb_range_four 3#usize (by rfl)
    · change (3#usize).val < (8#usize).val
      scalar_tac
    · change (4#usize).val = (3#usize).val + 1
      scalar_tac
    · rfl
  have hn4 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_four =
      .ok (some 4#usize, limb_range_five) := by
    apply range_next_to_literal limb_range_four limb_range_five 4#usize (by rfl)
    · change (4#usize).val < (8#usize).val
      scalar_tac
    · change (5#usize).val = (4#usize).val + 1
      scalar_tac
    · rfl
  have hn5 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_five =
      .ok (some 5#usize, limb_range_six) := by
    apply range_next_to_literal limb_range_five limb_range_six 5#usize (by rfl)
    · change (5#usize).val < (8#usize).val
      scalar_tac
    · change (6#usize).val = (5#usize).val + 1
      scalar_tac
    · rfl
  have hn6 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_six =
      .ok (some 6#usize, limb_range_seven) := by
    apply range_next_to_literal limb_range_six limb_range_seven 6#usize (by rfl)
    · change (6#usize).val < (8#usize).val
      scalar_tac
    · change (7#usize).val = (6#usize).val + 1
      scalar_tac
    · rfl
  have hn7 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_seven =
      .ok (some 7#usize, limb_range_eight) := by
    apply range_next_to_literal limb_range_seven limb_range_eight 7#usize (by rfl)
    · change (7#usize).val < (8#usize).val
      scalar_tac
    · change (8#usize).val = (7#usize).val + 1
      scalar_tac
    · rfl
  have hb0 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_zero limb_range_one sums sums1 scalar 0#usize hn0 h0
  have hb1 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_one limb_range_two sums1 sums2 scalar 1#usize hn1 h1
  have hb2 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_two limb_range_three sums2 sums3 scalar 2#usize hn2 h2
  have hb3 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_three limb_range_four sums3 sums4 scalar 3#usize hn3 h3
  have hb4 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_four limb_range_five sums4 sums5 scalar 4#usize hn4 h4
  have hb5 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_five limb_range_six sums5 sums6 scalar 5#usize hn5 h5
  have hb6 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_six limb_range_seven sums6 sums7 scalar 6#usize hn6 h6
  have hb7 := explicit_segment_at_success_calls_old_inner_body
    ops coefficient limb_range_seven limb_range_eight sums7 sums8 scalar 7#usize hn7 h7
  have hnext8 : core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_eight =
      .ok (none, limb_range_eight) := by
    apply range_next_done limb_range_eight
    change (8#usize).val ≥ (8#usize).val
    exact le_rfl
  have hdone : OldInnerBody ops coefficient limb_range_eight sums8 scalar =
      .ok (.done sums8) := by
    change (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize limb_range_eight
      match o with
      | none => ok (done sums8)
      | some limb => do
        let i ← Array.index_usize coefficient limb
        let i1 ← lift (core.convert.num.FromU64U32.from i)
        let i2 ← lift (core.convert.num.FromU64U32.from scalar)
        let i3 ← i1 * i2
        let i4 ← Array.index_usize sums8 limb
        let i5 ← i4 + i3
        let a ← Array.update sums8 limb i5
        ok (cont (iter1, a, scalar))) = .ok (.done sums8)
    rw [hnext8]
    rfl
  have hloop : OldInnerLoop ops limb_range_zero sums scalar coefficient = .ok sums8 := by
    change Aeneas.Std.loop (oldInnerStep ops coefficient)
      (limb_range_zero, sums, scalar) = .ok sums8
    exact loop_success_of_eight_steps (oldInnerStep ops coefficient)
      (limb_range_zero, sums, scalar) (limb_range_one, sums1, scalar)
      (limb_range_two, sums2, scalar) (limb_range_three, sums3, scalar)
      (limb_range_four, sums4, scalar) (limb_range_five, sums5, scalar)
      (limb_range_six, sums6, scalar) (limb_range_seven, sums7, scalar)
      (limb_range_eight, sums8, scalar) sums8
      (by simpa [oldInnerStep] using hb0)
      (by simpa [oldInnerStep] using hb1)
      (by simpa [oldInnerStep] using hb2)
      (by simpa [oldInnerStep] using hb3)
      (by simpa [oldInnerStep] using hb4)
      (by simpa [oldInnerStep] using hb5)
      (by simpa [oldInnerStep] using hb6)
      (by simpa [oldInnerStep] using hb7)
      (by simpa [oldInnerStep] using hdone)
  exact ⟨term, bytes, wide, coefficient, scalar, sums1, sums2, sums3, sums4,
    sums5, sums6, sums7, sums8, hread, hcoeff, hparse, h0, h1, h2, h3,
    h4, h5, h6, h7, hfinal, by simpa [hfinal] using hloop⟩


#print axioms one_coordinate_calls_old_inner_body
#print axioms explicit_segment_zero_success_calls_old_inner_body
#print axioms explicit_segment_at_success_calls_old_inner_body
#print axioms range_next_success
#print axioms loop_success_of_eight_steps
#print axioms new_term_body_success_exposes_first_segment
#print axioms new_term_body_success_runs_old_inner_body_first
#print axioms new_term_body_success_exposes_eight_segments
#print axioms new_term_body_success_supplies_old_inner_loop

end AspisR1FastDotsFixedInnerBodyStepBridgeV1
