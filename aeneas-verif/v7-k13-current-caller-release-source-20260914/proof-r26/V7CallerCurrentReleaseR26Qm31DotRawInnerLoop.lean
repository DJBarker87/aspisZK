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

#print axioms canonicalM31Sum_spec
#print axioms generated_raw_component_body_step_exact
#print axioms generated_raw_inner_loop_exact
#print axioms raw_component_step_corresponds

end V7CallerCurrentReleaseR26Qm31DotRawInnerLoop
