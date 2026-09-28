import V7CallerCurrentReleaseR26Qm31DotRawComponentSemantics

/-!
# Complete generated three-component raw QM31-dot loop

The source iterator has exactly three components.  We give its symbolic fold
and prove the generated loop returns that fold without unfolding its bodies.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawInnerLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26Qm31DotInnerIterator
open V7CallerCurrentReleaseR26Qm31DotRawComponent
open V7CallerCurrentReleaseR26Qm31DotRawComponentSemantics

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev Pair := CM31 × CM31
abbrev Raw := Array Std.U64 9#usize
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev PairIterator := core.array.iter.IntoIter Pair 3#usize
abbrev EnumeratedPairIterator :=
  core.iter.adapters.enumerate.Enumerate PairIterator

local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩

/-- The unique canonical output of generated M31 addition. -/
noncomputable def canonicalM31Sum (left right : M31) : M31 :=
  by
    classical
    exact if h : GeneratedCanonicalM31 left ∧
        GeneratedCanonicalM31 right then
      Classical.choose
        (generated_m31_add_corresponds left right h.1 h.2)
    else field.M31.ZERO

theorem canonicalM31Sum_spec (left right : M31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right) :
    field.M31.add left right = ok (canonicalM31Sum left right) ∧
      GeneratedCanonicalM31 (canonicalM31Sum left right) ∧
      generatedM31ToExact (canonicalM31Sum left right) =
        generatedM31ToExact left + generatedM31ToExact right := by
  classical
  rw [canonicalM31Sum, dif_pos ⟨leftCanonical, rightCanonical⟩]
  simpa [generatedM31ToExact] using
    (Classical.choose_spec
      (generated_m31_add_corresponds left right
        leftCanonical rightCanonical))

noncomputable def rawComponentStep
    (raw : Raw) (component : Nat) (pair : Pair) : Raw :=
  accumulateRawComponent raw (usizeOfNatTruncate component)
    pair.1 pair.2
    (canonicalM31Sum pair.1.a pair.1.b)
    (canonicalM31Sum pair.2.a pair.2.b)

noncomputable def rawAfterComponents
    (pairs : Array Pair 3#usize) (base : Raw) : Nat → Raw
  | 0 => base
  | processed + 1 =>
      if processed < 3 then
        rawComponentStep (rawAfterComponents pairs base processed) processed
          pairs.val[processed]!
      else rawAfterComponents pairs base processed

theorem generated_raw_component_body_step_exact
    (pairs : Array Pair 3#usize) (raw : Raw) (processed : Nat)
    (active : processed < 3)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2) :
    field.qm31_dot_loop0_loop0_loop0.body
        (expectedPairIterator pairs processed) raw =
      ok (cont
        (expectedPairIterator pairs (processed + 1),
          rawComponentStep raw processed pairs.val[processed]!)) := by
  obtain ⟨leftSum, rightSum, bodyRun, leftRun, rightRun,
      _leftCanonical, _rightCanonical, _leftExact, _rightExact⟩ :=
    generated_raw_component_body_step pairs raw processed active pairsCanonical
  obtain ⟨leftCanonical, rightCanonical⟩ :=
    pairsCanonical processed active
  have leftSpec := canonicalM31Sum_spec
    pairs.val[processed]!.1.a pairs.val[processed]!.1.b
      leftCanonical.1 leftCanonical.2
  have rightSpec := canonicalM31Sum_spec
    pairs.val[processed]!.2.a pairs.val[processed]!.2.b
      rightCanonical.1 rightCanonical.2
  have leftExact : leftSum = canonicalM31Sum
      pairs.val[processed]!.1.a pairs.val[processed]!.1.b :=
    Result.ok.inj (leftRun.symm.trans leftSpec.1)
  have rightExact : rightSum = canonicalM31Sum
      pairs.val[processed]!.2.a pairs.val[processed]!.2.b :=
    Result.ok.inj (rightRun.symm.trans rightSpec.1)
  simpa [rawComponentStep, leftExact, rightExact] using bodyRun

private theorem generated_raw_component_body_done
    (pairs : Array Pair 3#usize) (raw : Raw) :
    field.qm31_dot_loop0_loop0_loop0.body
        (expectedPairIterator pairs 3) raw = ok (done raw) := by
  unfold field.qm31_dot_loop0_loop0_loop0.body
  rw [expected_pair_iterator_done]
  simp

/-- The complete generated iterator returns the three-step symbolic fold. -/
theorem generated_raw_inner_loop_exact
    (pairs : Array Pair 3#usize) (base : Raw)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2) :
    field.qm31_dot_loop0_loop0_loop0 (expectedPairIterator pairs 0) base =
      ok (rawAfterComponents pairs base 3) := by
  have loopSpec :
      field.qm31_dot_loop0_loop0_loop0 (expectedPairIterator pairs 0) base
        ⦃ result => result = rawAfterComponents pairs base 3 ⦄ := by
    unfold field.qm31_dot_loop0_loop0_loop0
    apply loop.spec_decr_nat
      (fun state : EnumeratedPairIterator × Raw =>
        3 - state.1.iter.index)
      (fun state => ∃ processed, processed ≤ 3 ∧
        state.1 = expectedPairIterator pairs processed ∧
        state.2 = rawAfterComponents pairs base processed)
      (fun result => result = rawAfterComponents pairs base 3)
    · rintro ⟨iter, raw⟩
        ⟨processed, processedBound, iterExact, rawExact⟩
      dsimp only at iterExact rawExact
      rw [iterExact, rawExact]
      dsimp only
      by_cases active : processed < 3
      · rw [generated_raw_component_body_step_exact pairs
            (rawAfterComponents pairs base processed) processed active
            pairsCanonical]
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨⟨processed + 1, by omega, rfl, ?_⟩, ?_⟩
        · simp [rawAfterComponents, active]
        · simp [expectedPairIterator]
          omega
      · have finished : processed = 3 := by omega
        subst processed
        rw [generated_raw_component_body_done]
        simp
    · exact ⟨0, by omega, rfl, rfl⟩
  obtain ⟨out, run, outExact⟩ := Aeneas.Std.WP.spec_imp_exists loopSpec
  simpa [outExact] using run

def ExactRawComponentStep
    (base out : Raw) (component : Nat) (pair : Pair) : Prop :=
  (out.val[component * 3]!.val : ExactM31) =
      (base.val[component * 3]!.val : ExactM31) +
        generatedM31ToExact pair.1.a * generatedM31ToExact pair.2.a ∧
    (out.val[component * 3 + 1]!.val : ExactM31) =
      (base.val[component * 3 + 1]!.val : ExactM31) +
        generatedM31ToExact pair.1.b * generatedM31ToExact pair.2.b ∧
    (out.val[component * 3 + 2]!.val : ExactM31) =
      (base.val[component * 3 + 2]!.val : ExactM31) +
        (generatedM31ToExact pair.1.a + generatedM31ToExact pair.1.b) *
          (generatedM31ToExact pair.2.a + generatedM31ToExact pair.2.b)

/-- A symbolic component step has the three expected field contributions and
does not modify another lane. -/
theorem raw_component_step_corresponds
    (base : Raw) (component : Nat) (pair : Pair)
    (componentBound : component < 3)
    (pairCanonical : GeneratedCanonicalCM31 pair.1 ∧
      GeneratedCanonicalCM31 pair.2)
    (bound0 : base.val[component * 3]!.val +
      rawM31Product pair.1.a pair.2.a < 2 ^ 64)
    (bound1 : base.val[component * 3 + 1]!.val +
      rawM31Product pair.1.b pair.2.b < 2 ^ 64)
    (bound2 : base.val[component * 3 + 2]!.val +
      rawM31Product (canonicalM31Sum pair.1.a pair.1.b)
        (canonicalM31Sum pair.2.a pair.2.b) < 2 ^ 64) :
    ExactRawComponentStep base (rawComponentStep base component pair)
        component pair ∧
      ∀ lane, lane < 9 →
        lane ≠ component * 3 →
        lane ≠ component * 3 + 1 →
        lane ≠ component * 3 + 2 →
        (rawComponentStep base component pair).val[lane]! = base.val[lane]! := by
  let componentWord := usizeOfNatTruncate component
  have componentVal : componentWord.val = component :=
    usizeOfNatTruncate_val_eq (small_fits_usize (by omega))
  have leftSpec := canonicalM31Sum_spec pair.1.a pair.1.b
    pairCanonical.1.1 pairCanonical.1.2
  have rightSpec := canonicalM31Sum_spec pair.2.a pair.2.b
    pairCanonical.2.1 pairCanonical.2.2
  have rawExact := accumulate_raw_component_exact base componentWord
    pair.1 pair.2 (canonicalM31Sum pair.1.a pair.1.b)
      (canonicalM31Sum pair.2.a pair.2.b) (by omega)
      pairCanonical.1 pairCanonical.2 leftSpec.2.1 rightSpec.2.1
      (by simpa [componentVal] using bound0)
      (by simpa [componentVal] using bound1)
      (by simpa [componentVal] using bound2)
  change ExactRawComponentStep base
      (accumulateRawComponent base componentWord pair.1 pair.2
        (canonicalM31Sum pair.1.a pair.1.b)
        (canonicalM31Sum pair.2.a pair.2.b)) component pair ∧ _
  rw [componentVal] at rawExact
  refine ⟨⟨?_, ?_, ?_⟩, rawExact.2.2.2⟩
  · have castExact := congrArg (fun value : Nat => (value : ExactM31))
      rawExact.1
    simpa [ExactRawComponentStep, rawM31Product, generatedM31ToExact]
      using castExact
  · have castExact := congrArg (fun value : Nat => (value : ExactM31))
      rawExact.2.1
    simpa [ExactRawComponentStep, rawM31Product, generatedM31ToExact]
      using castExact
  · have castExact := congrArg (fun value : Nat => (value : ExactM31))
      rawExact.2.2.1
    have leftExact :
        (((canonicalM31Sum pair.1.a pair.1.b).val : Nat) : ExactM31) =
          generatedM31ToExact pair.1.a + generatedM31ToExact pair.1.b := by
      simpa [generatedM31ToExact] using leftSpec.2.2
    have rightExact :
        (((canonicalM31Sum pair.2.a pair.2.b).val : Nat) : ExactM31) =
          generatedM31ToExact pair.2.a + generatedM31ToExact pair.2.b := by
      simpa [generatedM31ToExact] using rightSpec.2.2
    unfold rawM31Product at castExact
    rw [Nat.cast_add, Nat.cast_mul] at castExact
    rw [leftExact, rightExact] at castExact
    exact castExact

def RawComponentBounds
    (base : Raw) (component : Nat) (pair : Pair) : Prop :=
  base.val[component * 3]!.val + rawM31Product pair.1.a pair.2.a < 2 ^ 64 ∧
    base.val[component * 3 + 1]!.val +
      rawM31Product pair.1.b pair.2.b < 2 ^ 64 ∧
    base.val[component * 3 + 2]!.val +
      rawM31Product (canonicalM31Sum pair.1.a pair.1.b)
        (canonicalM31Sum pair.2.a pair.2.b) < 2 ^ 64

private theorem exact_component_transport
    (base before after : Raw) (component : Nat) (pair : Pair)
    (exact : ExactRawComponentStep base before component pair)
    (lane0 : after.val[component * 3]! = before.val[component * 3]!)
    (lane1 : after.val[component * 3 + 1]! =
      before.val[component * 3 + 1]!)
    (lane2 : after.val[component * 3 + 2]! =
      before.val[component * 3 + 2]!) :
    ExactRawComponentStep base after component pair := by
  unfold ExactRawComponentStep at exact ⊢
  rw [lane0, lane1, lane2]
  exact exact

/-- After all three pair components, every group of three raw lanes contains
the exact Karatsuba contribution for its corresponding CM31 pair. -/
theorem raw_after_components_three_corresponds
    (pairs : Array Pair 3#usize) (base : Raw)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2)
    (bounds : ∀ component, component < 3 →
      RawComponentBounds base component pairs.val[component]!) :
    ∀ component, component < 3 →
      ExactRawComponentStep base (rawAfterComponents pairs base 3)
        component pairs.val[component]! := by
  let pair0 := pairs.val[0]!
  let pair1 := pairs.val[1]!
  let pair2 := pairs.val[2]!
  let raw0 := rawComponentStep base 0 pair0
  let raw1 := rawComponentStep raw0 1 pair1
  let raw2 := rawComponentStep raw1 2 pair2
  have canonical0 := pairsCanonical 0 (by omega)
  have canonical1 := pairsCanonical 1 (by omega)
  have canonical2 := pairsCanonical 2 (by omega)
  have bounds0 := bounds 0 (by omega)
  have bounds1 := bounds 1 (by omega)
  have bounds2 := bounds 2 (by omega)
  have step0 : ExactRawComponentStep base raw0 0 pair0 ∧
      ∀ lane, lane < 9 → lane ≠ 0 → lane ≠ 1 → lane ≠ 2 →
        raw0.val[lane]! = base.val[lane]! := by
    simpa [raw0, pair0, RawComponentBounds] using
      (raw_component_step_corresponds base 0 pair0 (by omega)
        canonical0 bounds0.1 bounds0.2.1 bounds0.2.2)
  have raw0Lane3 : raw0.val[3]! = base.val[3]! :=
    step0.2 3 (by omega) (by omega) (by omega) (by omega)
  have raw0Lane4 : raw0.val[4]! = base.val[4]! :=
    step0.2 4 (by omega) (by omega) (by omega) (by omega)
  have raw0Lane5 : raw0.val[5]! = base.val[5]! :=
    step0.2 5 (by omega) (by omega) (by omega) (by omega)
  have step1 : ExactRawComponentStep raw0 raw1 1 pair1 ∧
      ∀ lane, lane < 9 → lane ≠ 3 → lane ≠ 4 → lane ≠ 5 →
        raw1.val[lane]! = raw0.val[lane]! := by
    apply raw_component_step_corresponds raw0 1 pair1 (by omega) canonical1
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw0Lane3
      rw [laneExact]
      simpa [RawComponentBounds, pair1] using bounds1.1
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw0Lane4
      rw [laneExact]
      simpa [RawComponentBounds, pair1] using bounds1.2.1
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw0Lane5
      rw [laneExact]
      simpa [RawComponentBounds, pair1] using bounds1.2.2
  have raw1Lane6 : raw1.val[6]! = base.val[6]! := by
    rw [step1.2 6 (by omega) (by omega) (by omega) (by omega),
      step0.2 6 (by omega) (by omega) (by omega) (by omega)]
  have raw1Lane7 : raw1.val[7]! = base.val[7]! := by
    rw [step1.2 7 (by omega) (by omega) (by omega) (by omega),
      step0.2 7 (by omega) (by omega) (by omega) (by omega)]
  have raw1Lane8 : raw1.val[8]! = base.val[8]! := by
    rw [step1.2 8 (by omega) (by omega) (by omega) (by omega),
      step0.2 8 (by omega) (by omega) (by omega) (by omega)]
  have step2 : ExactRawComponentStep raw1 raw2 2 pair2 ∧
      ∀ lane, lane < 9 → lane ≠ 6 → lane ≠ 7 → lane ≠ 8 →
        raw2.val[lane]! = raw1.val[lane]! := by
    apply raw_component_step_corresponds raw1 2 pair2 (by omega) canonical2
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw1Lane6
      rw [laneExact]
      simpa [RawComponentBounds, pair2] using bounds2.1
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw1Lane7
      rw [laneExact]
      simpa [RawComponentBounds, pair2] using bounds2.2.1
    · have laneExact := congrArg (fun word : Std.U64 => word.val) raw1Lane8
      rw [laneExact]
      simpa [RawComponentBounds, pair2] using bounds2.2.2
  have exact0Raw1 : ExactRawComponentStep base raw1 0 pair0 :=
    exact_component_transport base raw0 raw1 0 pair0 step0.1
      (step1.2 0 (by omega) (by omega) (by omega) (by omega))
      (step1.2 1 (by omega) (by omega) (by omega) (by omega))
      (step1.2 2 (by omega) (by omega) (by omega) (by omega))
  have exact0Raw2 : ExactRawComponentStep base raw2 0 pair0 :=
    exact_component_transport base raw1 raw2 0 pair0 exact0Raw1
      (step2.2 0 (by omega) (by omega) (by omega) (by omega))
      (step2.2 1 (by omega) (by omega) (by omega) (by omega))
      (step2.2 2 (by omega) (by omega) (by omega) (by omega))
  have exact1Raw1 : ExactRawComponentStep base raw1 1 pair1 := by
    have exact := step1.1
    unfold ExactRawComponentStep at exact ⊢
    rw [raw0Lane3, raw0Lane4, raw0Lane5] at exact
    norm_num at exact ⊢
    exact exact
  have exact1Raw2 : ExactRawComponentStep base raw2 1 pair1 :=
    exact_component_transport base raw1 raw2 1 pair1 exact1Raw1
      (step2.2 3 (by omega) (by omega) (by omega) (by omega))
      (step2.2 4 (by omega) (by omega) (by omega) (by omega))
      (step2.2 5 (by omega) (by omega) (by omega) (by omega))
  have exact2Raw2 : ExactRawComponentStep base raw2 2 pair2 := by
    have exact := step2.1
    unfold ExactRawComponentStep at exact ⊢
    rw [raw1Lane6, raw1Lane7, raw1Lane8] at exact
    norm_num at exact ⊢
    exact exact
  have finalRaw : rawAfterComponents pairs base 3 = raw2 := by
    simp [rawAfterComponents, raw2, raw1, raw0, pair0, pair1, pair2]
  intro component componentBound
  rw [finalRaw]
  have componentCases : component = 0 ∨ component = 1 ∨ component = 2 := by
    omega
  rcases componentCases with rfl | rfl | rfl
  · simpa [pair0] using exact0Raw2
  · simpa [pair1] using exact1Raw2
  · simpa [pair2] using exact2Raw2

#print axioms canonicalM31Sum_spec
#print axioms generated_raw_component_body_step_exact
#print axioms generated_raw_inner_loop_exact
#print axioms raw_component_step_corresponds
#print axioms raw_after_components_three_corresponds

end V7CallerCurrentReleaseR26Qm31DotRawInnerLoop
