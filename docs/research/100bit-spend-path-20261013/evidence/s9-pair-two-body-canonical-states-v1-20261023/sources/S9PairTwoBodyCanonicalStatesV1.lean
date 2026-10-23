import S9PairTwoBodyCallsV1
import S9PairSideZeroBodyCanonicalV1
import S9PairSideOneBodyFullArrayCanonicalV1
import S3S9TransparentFoldS2InstanceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9PairTwoBodyCanonicalStatesV1

abbrev U := Std.Usize
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PairArray := Array PW (4#usize)
abbrev PairQArray := Array PQ (2#usize)
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev P6Q := AspisR1S9HelperP6.field.QM31
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev PairMapQ := AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
abbrev P6MapW := AspisR1S9CandidateHelperV1.toP6W
abbrev P6MapQ := AspisR1S9CandidateHelperV1.toP6Q
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem read_success_bound {A : Type} {N : Usize}
    (a : Array A N) (i : U) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

private theorem pair_zero_maps_candidate :
    PairMapW AspisR1S9PairCallerStepV1.field.WideExact.ZERO =
      AspisR1S9CandidateHelperV1.field.WideExact.ZERO := by
  simp [PairMapW, AspisR1S9PairCallerCandidateMapV1.pairToCandidateW,
    AspisR1S9PairCallerStepV1.toP6W, AspisR1S9CandidateHelperV1.fromP6W,
    AspisR1S9PairCallerStepV1.field.WideExact.ZERO,
    AspisR1S9CandidateHelperV1.field.WideExact.ZERO,
    AspisR1S9PairCallerStepV1.field.QM31.ZERO,
    AspisR1S9CandidateHelperV1.field.QM31.ZERO,
    AspisR1S9PairCallerStepV1.toP6Q, AspisR1S9CandidateHelperV1.fromP6Q,
    AspisR1S9PairCallerStepV1.toP6CM, AspisR1S9CandidateHelperV1.fromP6CM,
    AspisR1S9PairCallerStepV1.toP6M, AspisR1S9CandidateHelperV1.fromP6M]

private theorem candidate_zero_maps_to_p6 :
    AspisR1S9CandidateHelperV1.toP6W
      AspisR1S9CandidateHelperV1.field.WideExact.ZERO =
      AspisR1S9HelperP6.field.WideExact.ZERO := by
  simp [AspisR1S9CandidateHelperV1.toP6W,
    AspisR1S9CandidateHelperV1.toP6Q,
    AspisR1S9CandidateHelperV1.toP6CM,
    AspisR1S9CandidateHelperV1.toP6M,
    AspisR1S9CandidateHelperV1.field.WideExact.ZERO,
    AspisR1S9CandidateHelperV1.field.QM31.ZERO,
    AspisR1S9HelperP6.field.WideExact.ZERO,
    AspisR1S9HelperP6.field.QM31.ZERO]

private theorem initial_zero_maps_to_p6 :
    mapArray P6MapW (mapArray PairMapW
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO)) =
    Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO := by
  unfold mapArray AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
  apply Subtype.ext
  simp [Array.repeat, PairMapW, P6MapW, pair_zero_maps_candidate,
    candidate_zero_maps_to_p6]

private theorem initial_zero_reads_canonical :
    ∀ (j : U) (v : P6W),
      Array.index_usize
        (mapArray P6MapW (mapArray PairMapW
          (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO))) j = .ok v →
      Canonical v := by
  intro j v hread
  rw [initial_zero_maps_to_p6] at hread
  have hj := read_success_bound
    (Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO) j v hread
  have hspec := Array.index_usize_spec
    (Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO) j hj
  rcases WP.spec_imp_exists hspec with ⟨z, hzread, hzval⟩
  have hj4 : j.val < 4 := by simpa using hj
  have hz : z = AspisR1S9HelperP6.field.WideExact.ZERO := by
    simpa only [Array.repeat_val, List.getElem_replicate] using hzval
  have hreadZero : Array.index_usize
      (Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO) j =
      .ok AspisR1S9HelperP6.field.WideExact.ZERO :=
    hzread.trans (congrArg Result.ok hz)
  have hv : v = AspisR1S9HelperP6.field.WideExact.ZERO := by
    apply Result.ok.inj
    exact hread.symm.trans hreadZero
  rw [hv]
  exact AspisR1S9TransparentFoldS2InstanceV1.zero_canonical

/-- Adapter for one exact generated Pair helper execution. The initial
weights are the helper's actual zero initialization; side zero produces the
intermediate array and its full mapped-read invariant, which is then the
weights contract consumed by side one. The returned body equations retain
both calls from the same loop witness for later source refinement. This is a
Pair-to-selected-helper adapter theorem, not an actual-source caller theorem. -/
theorem successful_pair_helper_two_body_states_canonical
    (ap0 ap1 : PairArray) (extra : PairQArray) (output : PairArray)
    (hhelper : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hap0 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap0)) j = .ok v → Canonical v)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
        AspisR1S9HighTermsTraceV1.canonicalW v)
    (hextra : ∀ (j : U) (v : P6Q),
      Array.index_usize (mapArray P6MapQ (mapArray PairMapQ extra)) j = .ok v →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM v)) :
    ∃ (iter1 iter2 : PR) (middle : PairArray),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
        AspisR1S9PairTwoBodyCallsV1.start0 = .ok (some 0#usize, iter1) ∧
      AspisR1S9PairTwoBodyCallsV1.body ap0 ap1 extra
        (AspisR1S9PairTwoBodyCallsV1.start0,
          Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) =
        .ok (.cont (iter1, middle)) ∧
      AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra 0#usize iter1
          (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) =
        .ok (.cont (iter1, middle)) ∧
      (∀ (j : U) (v : P6W),
        Array.index_usize (mapArray P6MapW (mapArray PairMapW middle)) j = .ok v →
          Canonical v) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1 =
        .ok (some iter1.start, iter2) ∧ iter1.start.val = 1 ∧
      AspisR1S9PairTwoBodyCallsV1.body ap0 ap1 extra (iter1, middle) =
        .ok (.cont (iter2, output)) ∧
      AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra 1#usize iter2 middle = .ok (.cont (iter2, output)) ∧
      (∀ (j : U) (v : P6W),
        Array.index_usize (mapArray P6MapW (mapArray PairMapW output)) j = .ok v →
          Canonical v) := by
  have hloop : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop
      AspisR1S9PairTwoBodyCallsV1.start0 ap0 ap1 extra
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) = .ok output := by
    unfold _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights at hhelper
    simpa only [bind_tc_ok, AspisR1S9PairTwoBodyCallsV1.start0] using hhelper
  obtain ⟨iter1, iter2, middle, hnext0, hstart1, _hend1, hbody0,
      hnext1, _hstart2, _hend2, hbody1, _hnext2, _hdone⟩ :=
    AspisR1S9PairTwoBodyCallsV1.helper_success_two_body_calls
      ap0 ap1 extra
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO)
      output hloop
  have hactive0 := hbody0
  change _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra AspisR1S9PairTwoBodyCallsV1.start0
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) =
      .ok (.cont (iter1, middle)) at hactive0
  rw [AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
    ap0 ap1 extra AspisR1S9PairTwoBodyCallsV1.start0 iter1 0#usize
    (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) hnext0] at hactive0
  have hside1 : iter1.start = 1#usize := UScalar.eq_of_val_eq hstart1
  have hactive1 := hbody1
  change _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter1 middle = .ok (.cont (iter2, output)) at hactive1
  rw [AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
    ap0 ap1 extra iter1 iter2 iter1.start middle hnext1] at hactive1
  have hactive1' : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
      ap0 ap1 extra 1#usize iter2 middle = .ok (.cont (iter2, output)) := by
    simpa only [hside1] using hactive1
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,t0,t1,t2,t3,perm3,
      first2,first3,all,productAll,productFirst3,mixed,weights1,zeroOut,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,hprefix,
      hadd2,hadd3,haddAll,hmulAll,hmulFirst3,hmixed,hupdate0,hupdate1,
      hlowCan,hfirst3Can,hallCan,hproductAllCan,hproductFirst3Can,hmixedCan,
      hzeroFlow,hzeroCan⟩ :=
    AspisR1S9PairSideZeroBodyCanonicalV1.pair_body_sidezero_success_canonical
    ap0 ap1 extra iter1
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO)
      (.cont (iter1, middle)) hactive0 hap0 hap1 hextra initial_zero_reads_canonical
  have hmiddleEq : zeroOut = middle := by
    have hflow : ControlFlow.cont (iter1, middle) = ControlFlow.cont (iter1, zeroOut) := hzeroFlow
    injection hflow with hp
    exact (congrArg Prod.snd hp).symm
  subst zeroOut
  have hmiddleCan := hzeroCan
  have hout := AspisR1S9PairSideOneBodyFullArrayCanonicalV1.side_one_active_body_output_array_canonical
    ap0 ap1 extra iter2 middle (.cont (iter2, output)) hactive1' hap0 hap1 hextra hmiddleCan
  obtain ⟨output1, houtFlow, houtCan⟩ := hout
  have houtEq : output1 = output := by
    have hflow : ControlFlow.cont (iter2, output1) = ControlFlow.cont (iter2, output) :=
      houtFlow.symm.trans (by rfl)
    exact congrArg Prod.snd (ControlFlow.cont.inj hflow)
  subst output1
  exact ⟨iter1, iter2, middle, hnext0, hbody0, hactive0, hmiddleCan,
    hnext1, hstart1, hbody1, hactive1', houtCan⟩

#print axioms successful_pair_helper_two_body_states_canonical

end AspisR1S9PairTwoBodyCanonicalStatesV1
