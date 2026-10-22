import S9BodyPrefixWitnessV1
import S9SideOneMeaningRootV1
import S9AfterSumsTailDispatchV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9BodyOneRecordConsumerV1

open AspisR1S9HelperP6
open AspisR1S9BodyPrefixSemanticsV1

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev decode := AspisR1S9CurrentFieldOpsV1.decode
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The generated post-sum source suffix and Result binds force the same
side-one tail operation to return the output carried by this exact activeBody
success. -/
theorem side_one_source_tail_success
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (pfx : BodyPrefixWitness ap0 ap1 extra 1#usize iterNext weights0
      (.cont (iterNext, output))) :
    AspisR1.S9SideOneTailRootV1.sideOneTail
      weights0 ap1 pfx.low pfx.all pfx.first2 pfx.q4 pfx.q16 = .ok output := by
  have hdispatch := AspisR1S9AfterSumsTailDispatchV1.afterSums_side_one
    ap1 weights0 iterNext pfx.low pfx.first2 pfx.first3 pfx.all pfx.q4 pfx.q16
  have hsums := pfx.afterSums
  rw [hdispatch] at hsums
  obtain ⟨tailOutput, htailOutput, hcont⟩ := bind_success_inv
    (AspisR1.S9SideOneTailRootV1.sideOneTail
      weights0 ap1 pfx.low pfx.all pfx.first2 pfx.q4 pfx.q16)
    (fun out => Result.ok (ControlFlow.cont (iterNext, out)))
    (ControlFlow.cont (iterNext, output)) hsums
  have hcont' := Result.ok.inj hcont
  have hpair := ControlFlow.cont.inj hcont'
  have htailEq : tailOutput = output := congrArg Prod.snd hpair
  subst tailOutput
  exact htailOutput

structure BodyOneOutputWitness
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W) where
  prefixData : BodyPrefixWitness ap0 ap1 extra 1#usize iterNext weights0
    (.cont (iterNext, output))
  permIndex : U
  last : field.WideExact
  permRead : Array.index_usize weights.PERM 3#usize = .ok permIndex
  ap1Read : Array.index_usize ap1 permIndex = .ok last
  output1Canonical : AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells output 1)
  output2Canonical : AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells output 2)
  output3Canonical : AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells output 3)
  outputMeaning : ∀ j : Fin 4, AspisR1S9CurrentFieldOpsV1.decode (AspisR1.S9ArrayWriteScheduleRootV1.cells output j) =
    if j.val = 0 then AspisR1S9CurrentFieldOpsV1.decode (AspisR1.S9ArrayWriteScheduleRootV1.cells weights0 j)
    else if j.val = 1 then AspisR1S9CurrentFieldOpsV1.decode (AspisR1.S9ArrayWriteScheduleRootV1.cells weights0 1) +
      AspisR1S9CurrentFieldOpsV1.decode prefixData.low * (AspisR1S9CurrentFieldOpsV1.decode last *
        AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER)
    else if j.val = 2 then (AspisR1S9CurrentFieldOpsV1.decode prefixData.low * AspisR1S9CurrentFieldOpsV1.decode prefixData.all) *
      algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM
        AspisWideTower.WideExact
        (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ prefixData.q4)
    else (AspisR1S9CurrentFieldOpsV1.decode prefixData.low * AspisR1S9CurrentFieldOpsV1.decode prefixData.first2) *
      (algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM
        AspisWideTower.WideExact
        (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ prefixData.q16) *
       algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM
        AspisWideTower.WideExact
        (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ prefixData.q4))

/-- Side-one branch semantics for the exact generic rich-prefix witness. The
same prefix record carries the generated `from_fn` result and ordered sums;
this consumer only adds the checked side-one tail and its returned-array
formula. -/
theorem side_one_tail_math_witness_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (pfx : BodyPrefixWitness ap0 ap1 extra 1#usize iterNext weights0
      (.cont (iterNext, output)))
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hweights0_1 : ∀ x, Array.index_usize weights0 1#usize = .ok x → Canonical x)
    (htail : AspisR1.S9SideOneTailRootV1.sideOneTail
      weights0 ap1 pfx.low pfx.all pfx.first2 pfx.q4 pfx.q16 = .ok output) :
    Nonempty (BodyOneOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  have hreadQ4 : Array.index_usize pfx.high 1#usize = .ok pfx.q4 := by
    rw [pfx.highArray]
    rfl
  have hq4Can' := pfx.highCanonical 1#usize pfx.q4 hreadQ4
  have hq4map : AspisR1S9GeneratedWideMulQM31V2.toQM pfx.q4 =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM pfx.q4 := by
    cases pfx.q4 <;> rfl
  have hq4Can : AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ pfx.q4 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM pfx.q4)
    rw [← hq4map]
    exact hq4Can'
  have hq16map : AspisR1S9GeneratedWideMulQM31V2.toQM pfx.q16 =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM pfx.q16 := by
    cases pfx.q16 <;> rfl
  have hq16Can : AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ pfx.q16 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM pfx.q16)
    rw [hq16map]
    exact pfx.q16Canonical
  obtain ⟨permIndex, last, hperm, hlast, hcell1Can, hcell2Can,
      hcell3Can, hformula⟩ :=
    AspisR1.S9SideOneMeaningRootV1.sideOneTail_success_exact
      weights0 ap1 pfx.low pfx.all pfx.first2 pfx.q4 pfx.q16 output
      pfx.lowCanonical pfx.allCanonical pfx.first2Canonical hq4Can hq16Can
      (fun x hx => hweights0_1 x hx) hp1 htail
  exact ⟨{ prefixData := pfx, permIndex := permIndex, last := last, permRead := hperm, ap1Read := hlast, output1Canonical := hcell1Can, output2Canonical := hcell2Can, output3Canonical := hcell3Can, outputMeaning := hformula }⟩


theorem side_one_prefix_tail_witness_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (pfx : BodyPrefixWitness ap0 ap1 extra 1#usize iterNext weights0
      (.cont (iterNext, output)))
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hweights0_1 : ∀ x, Array.index_usize weights0 1#usize = .ok x → Canonical x) :
    Nonempty (BodyOneOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  exact side_one_tail_math_witness_nonempty ap0 ap1 extra iterNext weights0 output
    pfx hp1 hweights0_1
    (side_one_source_tail_success ap0 ap1 extra iterNext weights0 output pfx)



/-- Construct the side-one result witness from the same successful generated
body call and its prefix contracts. The prefix remains attached to the exact
returned output and callback trace. -/
theorem body_one_output_witness_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 1#usize iterNext weights0 =
        .ok (.cont (iterNext, output)))
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x)
    (hweights0_1 : ∀ x,
      Array.index_usize weights0 1#usize = .ok x → Canonical x) :
    Nonempty (BodyOneOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  obtain ⟨p⟩ := body_prefix_witness_nonempty ap0 ap1 extra 1#usize
    iterNext weights0 (.cont (iterNext, output)) hactive hp0 hp1 hextra
  exact side_one_prefix_tail_witness_nonempty ap0 ap1 extra iterNext weights0 output p
    hp1 hweights0_1

noncomputable def body_one_output_witness
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 1#usize iterNext weights0 =
        .ok (.cont (iterNext, output)))
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x)
    (hweights0_1 : ∀ x,
      Array.index_usize weights0 1#usize = .ok x → Canonical x) :
    BodyOneOutputWitness ap0 ap1 extra iterNext weights0 output :=
  Classical.choice (body_one_output_witness_nonempty ap0 ap1 extra iterNext
    weights0 output hactive hp0 hp1 hextra hweights0_1)

end AspisR1S9BodyOneRecordConsumerV1
