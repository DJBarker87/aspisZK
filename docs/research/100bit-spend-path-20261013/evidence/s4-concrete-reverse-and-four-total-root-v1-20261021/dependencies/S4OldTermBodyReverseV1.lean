import NewTermBodyOldBodyBridgeV1
import S4OldInnerLoopReverseV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsOldTermBodyReverseV1

abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U32 := UScalar UScalarTy.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev M31 := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.M31
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.Ops
abbrev OldBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldBody
abbrev NewBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.NewBody

private theorem result_bind_assoc {α β γ : Type} (m : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do let y ← (do let x ← m; f x); g y) =
      (do let x ← m; let y ← f x; g y) := by
  cases m <;> rfl

private def explicitEight (coefficient : Array U32 8#usize)
    (sums : Array U64 8#usize) (scalar : M31) : Result (Array U64 8#usize) := do
  let s1 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient sums scalar 0#usize
  let s2 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s1 scalar 1#usize
  let s3 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s2 scalar 2#usize
  let s4 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s3 scalar 3#usize
  let s5 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s4 scalar 4#usize
  let s6 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s5 scalar 5#usize
  let s7 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s6 scalar 6#usize
  let s8 ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at coefficient s7 scalar 7#usize
  ok s8

private def flatEight (coefficient : Array U32 8#usize)
    (sums : Array U64 8#usize) (scalar : M31) : Result (Array U64 8#usize) := do
  let i5 ← Array.index_usize coefficient 0#usize
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 ← lift (core.convert.num.FromU64U32.from scalar)
  let i8 ← i6 * i7
  let i9 ← Array.index_usize sums 0#usize
  let i10 ← i9 + i8
  let sums1 ← Array.update sums 0#usize i10
  let i11 ← Array.index_usize coefficient 1#usize
  let i12 ← lift (core.convert.num.FromU64U32.from i11)
  let i13 ← lift (core.convert.num.FromU64U32.from scalar)
  let i14 ← i12 * i13
  let i15 ← Array.index_usize sums1 1#usize
  let i16 ← i15 + i14
  let sums2 ← Array.update sums1 1#usize i16
  let i17 ← Array.index_usize coefficient 2#usize
  let i18 ← lift (core.convert.num.FromU64U32.from i17)
  let i19 ← lift (core.convert.num.FromU64U32.from scalar)
  let i20 ← i18 * i19
  let i21 ← Array.index_usize sums2 2#usize
  let i22 ← i21 + i20
  let sums3 ← Array.update sums2 2#usize i22
  let i23 ← Array.index_usize coefficient 3#usize
  let i24 ← lift (core.convert.num.FromU64U32.from i23)
  let i25 ← lift (core.convert.num.FromU64U32.from scalar)
  let i26 ← i24 * i25
  let i27 ← Array.index_usize sums3 3#usize
  let i28 ← i27 + i26
  let sums4 ← Array.update sums3 3#usize i28
  let i29 ← Array.index_usize coefficient 4#usize
  let i30 ← lift (core.convert.num.FromU64U32.from i29)
  let i31 ← lift (core.convert.num.FromU64U32.from scalar)
  let i32 ← i30 * i31
  let i33 ← Array.index_usize sums4 4#usize
  let i34 ← i33 + i32
  let sums5 ← Array.update sums4 4#usize i34
  let i35 ← Array.index_usize coefficient 5#usize
  let i36 ← lift (core.convert.num.FromU64U32.from i35)
  let i37 ← lift (core.convert.num.FromU64U32.from scalar)
  let i38 ← i36 * i37
  let i39 ← Array.index_usize sums5 5#usize
  let i40 ← i39 + i38
  let sums6 ← Array.update sums5 5#usize i40
  let i41 ← Array.index_usize coefficient 6#usize
  let i42 ← lift (core.convert.num.FromU64U32.from i41)
  let i43 ← lift (core.convert.num.FromU64U32.from scalar)
  let i44 ← i42 * i43
  let i45 ← Array.index_usize sums6 6#usize
  let i46 ← i45 + i44
  let sums7 ← Array.update sums6 6#usize i46
  let i47 ← Array.index_usize coefficient 7#usize
  let i48 ← lift (core.convert.num.FromU64U32.from i47)
  let i49 ← lift (core.convert.num.FromU64U32.from scalar)
  let i50 ← i48 * i49
  let i51 ← Array.index_usize sums7 7#usize
  let i52 ← i51 + i50
  Array.update sums7 7#usize i52

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bind_pair_ok {α β γ : Type} (a : α) (b : β)
    (f : α → β → Result γ) :
    (do let (x, y) ← (ok (a, b) : Result (α × β)); f x y) = f a b := rfl

private theorem emitted_segment_continuation {β : Type}
    (coefficient : Array U32 8#usize) (sums : Array U64 8#usize)
    (scalar : M31) (limb : Usize) (k : Array U64 8#usize → Result β)
    (updated : Array U64 8#usize) (out : β)
    (hsegment : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
      coefficient sums scalar limb = .ok updated)
    (htail : k updated = .ok out) :
    (do
      let c ← Array.index_usize coefficient limb
      let c64 ← lift (core.convert.num.FromU64U32.from c)
      let s64 ← lift (core.convert.num.FromU64U32.from scalar)
      let product ← c64 * s64
      let oldSum ← Array.index_usize sums limb
      let newSum ← oldSum + product
      let next ← Array.update sums limb newSum
      k next) = .ok out := by
  have h : (do
      let next ← AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient sums scalar limb
      k next) = .ok out := by
    rw [hsegment]
    exact htail
  simpa only [AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at,
    result_bind_assoc] using h

theorem old_body_success_new_body
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hbody : OldBody ops q g slot iter sums = .ok (.cont (iter', sums'))) :
    NewBody ops q g slot iter sums = .ok (.cont (iter', sums')) := by
  unfold OldBody at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases pair with ⟨option, iter1⟩
  cases option with
  | none => cases Result.ok.inj hrest
  | some term =>
    obtain ⟨i, hi, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨i1, hi1, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨i2, hi2, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨i3, hi3, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨i4, hi4, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨bytesSlice, hs, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨parsedArray, hr, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨bytes, hbytes, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨parsed, hparse, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨scalar, hscalar, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨wide, hread, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨coefficient, hcoeff, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨limbCount, hlimbCount, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨oldSumsOut, hloop, hfinal⟩ := bind_success _ _ _ hrest
    have hpair : (iter1, oldSumsOut) = (iter', sums') := by
      exact ControlFlow.cont.inj (Result.ok.inj hfinal)
    have hiter : iter1 = iter' := congrArg Prod.fst hpair
    have hsums : oldSumsOut = sums' := congrArg Prod.snd hpair
    have hi23 : i2 = i3 := Result.ok.inj (hi2.symm.trans hi3)
    have hi4' : (i2 + 4#usize : Result Usize) = .ok i4 := by
      simpa [hi23] using hi4
    have hcount' : limbCount = 8#usize := by
      rw [hcount] at hlimbCount
      exact (Result.ok.inj hlimbCount).symm
    subst limbCount
    have hloop' : AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldInnerLoop
        ops { start := 0#usize, «end» := 8#usize } sums scalar coefficient = .ok oldSumsOut := hloop
    have htrace := AspisR1FastDotsOldInnerLoopReverseV1.old_inner_loop_success_trace
      ops coefficient scalar { start := 0#usize, «end» := 8#usize } sums oldSumsOut
      (by scalar_tac) hloop'
    obtain ⟨trace⟩ := htrace
    obtain ⟨s1,s2,s3,s4,s5,s6,s7,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
      AspisR1FastDotsOldInnerLoopReverseV1.trace_eight_segment_successes
        coefficient scalar sums sums oldSumsOut trace
    change AspisR1FastDotsOldInnerLoopReverseV1.segment
        coefficient s7 scalar 7#usize = .ok oldSumsOut at h7
    have h7' : AspisR1FastDotsOldInnerLoopReverseV1.segment
        coefficient s7 scalar 7#usize = .ok sums' := by
      simpa only [hsums] using h7
    have h0' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient sums scalar 0#usize = .ok s1 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient sums scalar 0#usize = .ok s1 at h0
      exact h0
    have h1' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s1 scalar 1#usize = .ok s2 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s1 scalar 1#usize = .ok s2 at h1
      exact h1
    have h2' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s2 scalar 2#usize = .ok s3 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s2 scalar 2#usize = .ok s3 at h2
      exact h2
    have h3' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s3 scalar 3#usize = .ok s4 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s3 scalar 3#usize = .ok s4 at h3
      exact h3
    have h4' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s4 scalar 4#usize = .ok s5 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s4 scalar 4#usize = .ok s5 at h4
      exact h4
    have h5' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s5 scalar 5#usize = .ok s6 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s5 scalar 5#usize = .ok s6 at h5
      exact h5
    have h6' : AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s6 scalar 6#usize = .ok s7 := by
      change AspisR1FastDotsFixedInnerBodyStepBridgeV1.explicit_segment_at
        coefficient s6 scalar 6#usize = .ok s7 at h6
      exact h6
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
        let i5 ← Array.index_usize coefficient 0#usize
        let i6 ← lift (core.convert.num.FromU64U32.from i5)
        let i7 ← lift (core.convert.num.FromU64U32.from scalar)
        let i8 ← i6 * i7
        let i9 ← Array.index_usize sums 0#usize
        let i10 ← i9 + i8
        let sums1 ← Array.update sums 0#usize i10
        let i11 ← Array.index_usize coefficient 1#usize
        let i12 ← lift (core.convert.num.FromU64U32.from i11)
        let i13 ← lift (core.convert.num.FromU64U32.from scalar)
        let i14 ← i12 * i13
        let i15 ← Array.index_usize sums1 1#usize
        let i16 ← i15 + i14
        let sums2 ← Array.update sums1 1#usize i16
        let i17 ← Array.index_usize coefficient 2#usize
        let i18 ← lift (core.convert.num.FromU64U32.from i17)
        let i19 ← lift (core.convert.num.FromU64U32.from scalar)
        let i20 ← i18 * i19
        let i21 ← Array.index_usize sums2 2#usize
        let i22 ← i21 + i20
        let sums3 ← Array.update sums2 2#usize i22
        let i23 ← Array.index_usize coefficient 3#usize
        let i24 ← lift (core.convert.num.FromU64U32.from i23)
        let i25 ← lift (core.convert.num.FromU64U32.from scalar)
        let i26 ← i24 * i25
        let i27 ← Array.index_usize sums3 3#usize
        let i28 ← i27 + i26
        let sums4 ← Array.update sums3 3#usize i28
        let i29 ← Array.index_usize coefficient 4#usize
        let i30 ← lift (core.convert.num.FromU64U32.from i29)
        let i31 ← lift (core.convert.num.FromU64U32.from scalar)
        let i32 ← i30 * i31
        let i33 ← Array.index_usize sums4 4#usize
        let i34 ← i33 + i32
        let sums5 ← Array.update sums4 4#usize i34
        let i35 ← Array.index_usize coefficient 5#usize
        let i36 ← lift (core.convert.num.FromU64U32.from i35)
        let i37 ← lift (core.convert.num.FromU64U32.from scalar)
        let i38 ← i36 * i37
        let i39 ← Array.index_usize sums5 5#usize
        let i40 ← i39 + i38
        let sums6 ← Array.update sums5 5#usize i40
        let i41 ← Array.index_usize coefficient 6#usize
        let i42 ← lift (core.convert.num.FromU64U32.from i41)
        let i43 ← lift (core.convert.num.FromU64U32.from scalar)
        let i44 ← i42 * i43
        let i45 ← Array.index_usize sums6 6#usize
        let i46 ← i45 + i44
        let sums7 ← Array.update sums6 6#usize i46
        let i47 ← Array.index_usize coefficient 7#usize
        let i48 ← lift (core.convert.num.FromU64U32.from i47)
        let i49 ← lift (core.convert.num.FromU64U32.from scalar)
        let i50 ← i48 * i49
        let i51 ← Array.index_usize sums7 7#usize
        let i52 ← i51 + i50
        let sums8 ← Array.update sums7 7#usize i52
        ok (ControlFlow.cont (iter1, sums8))) = .ok (.cont (iter', sums'))
    rw [hnext]
    simp only [bind_tc_ok, bind_pair_ok, hi, hi1, hi2, hi4', hs, hr, hbytes,
      hparse, hscalar, hread, hcoeff, hiter]
    apply emitted_segment_continuation coefficient sums scalar 0#usize _ s1 _ h0'
    apply emitted_segment_continuation coefficient s1 scalar 1#usize _ s2 _ h1'
    apply emitted_segment_continuation coefficient s2 scalar 2#usize _ s3 _ h2'
    apply emitted_segment_continuation coefficient s3 scalar 3#usize _ s4 _ h3'
    apply emitted_segment_continuation coefficient s4 scalar 4#usize _ s5 _ h4'
    apply emitted_segment_continuation coefficient s5 scalar 5#usize _ s6 _ h5'
    apply emitted_segment_continuation coefficient s6 scalar 6#usize _ s7 _ h6'
    apply emitted_segment_continuation coefficient s7 scalar 7#usize
      (fun sums8 => ok (ControlFlow.cont (iter', sums8))) sums' (.cont (iter', sums')) h7'
    rfl

#print axioms old_body_success_new_body

end AspisR1FastDotsOldTermBodyReverseV1
