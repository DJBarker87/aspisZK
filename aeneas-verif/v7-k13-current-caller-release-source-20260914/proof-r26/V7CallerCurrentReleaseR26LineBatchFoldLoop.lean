import V7CallerCurrentReleaseR26LineBatchFoldStep
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Exact current line-batch fold traversal

The generated loop updates every line scale and coordinate in place.  This
file lifts the one-entry arithmetic theorem to the complete successful loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26LineBatchFoldLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFoldStep
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev FoldState := Slice RawQM31 × Slice RawM31 × Std.Usize

local instance : Inhabited RawM31 := ⟨0#u32⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

/-- Shared line-slice accessors fix the generated fallback instances once, so
cross-module semantic statements use definitionally identical raw entries. -/
def lineQM31At (values : Slice RawQM31) (index : Nat) : RawQM31 :=
  values.val[index]!

def lineM31At (values : Slice RawM31) (index : Nat) : RawM31 :=
  values.val[index]!

def CanonicalQM31Slice (values : Slice RawQM31) : Prop :=
  ∀ index, index < values.val.length →
    GeneratedCanonicalQM31 values.val[index]!

def CanonicalM31Slice (values : Slice RawM31) : Prop :=
  ∀ index, index < values.val.length →
    GeneratedCanonicalM31 values.val[index]!

structure FoldPrefix
    (alpha : ExactQM31) (baseScales : Slice RawQM31)
    (baseXs : Slice RawM31) (state : FoldState) : Prop where
  stateScalesLength : state.1.val.length = baseScales.val.length
  stateXsLength : state.2.1.val.length = baseXs.val.length
  baseLengths : baseXs.val.length = baseScales.val.length
  baseLength : baseScales.val.length = 16
  extentBound : state.2.2.val ≤ baseScales.val.length
  currentScalesCanonical : CanonicalQM31Slice state.1
  currentXsCanonical : CanonicalM31Slice state.2.1
  processed : ∀ index, index < state.2.2.val →
      generatedQm31ToExact state.1.val[index]! =
        generatedQm31ToExact baseScales.val[index]! *
          lineBatchFoldNumerator alpha
            (generatedM31ToExact baseXs.val[index]!) ∧
      generatedM31ToExact state.2.1.val[index]! =
        doubledM31 (doubledM31
          (generatedM31ToExact baseXs.val[index]!))
  untouched : ∀ index, state.2.2.val ≤ index →
      index < baseScales.val.length →
      state.1.val[index]! = baseScales.val[index]! ∧
      state.2.1.val[index]! = baseXs.val[index]!

/-- Exact result for one completed line entry. -/
structure LineEntryExact
    (alpha : ExactQM31) (baseScales : Slice RawQM31)
    (baseXs : Slice RawM31) (scalesOut : Slice RawQM31)
    (xsOut : Slice RawM31) (index : Nat) : Prop where
  scale : generatedQm31ToExact (lineQM31At scalesOut index) =
    generatedQm31ToExact (lineQM31At baseScales index) *
        lineBatchFoldNumerator alpha
          (generatedM31ToExact (lineM31At baseXs index))
  x : generatedM31ToExact (lineM31At xsOut index) =
    doubledM31 (doubledM31
      (generatedM31ToExact (lineM31At baseXs index)))

private theorem sliceSetSame
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (value : T) (bound : index.val < values.val.length) :
    (values.set index value).val[index.val]! = value := by
  simp only [Slice.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨bound, rfl⟩

private theorem sliceSetNe
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (value : T) (other : Nat) (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

private theorem sliceSetLength
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (value : T) :
    (values.set index value).val.length = values.val.length := by
  simp [Slice.set_val_eq]

private theorem canonicalQM31Set
    (values : Slice RawQM31) (index : Std.Usize) (value : RawQM31)
    (bound : index.val < values.val.length)
    (hvalues : CanonicalQM31Slice values)
    (hvalue : GeneratedCanonicalQM31 value) :
    CanonicalQM31Slice (values.set index value) := by
  intro other hother
  by_cases same : other = index.val
  · subst other
    rw [sliceSetSame values index value bound]
    exact hvalue
  · rw [sliceSetNe values index value other same]
    apply hvalues other
    simpa [sliceSetLength] using hother

private theorem canonicalM31Set
    (values : Slice RawM31) (index : Std.Usize) (value : RawM31)
    (bound : index.val < values.val.length)
    (hvalues : CanonicalM31Slice values)
    (hvalue : GeneratedCanonicalM31 value) :
    CanonicalM31Slice (values.set index value) := by
  intro other hother
  by_cases same : other = index.val
  · subst other
    rw [sliceSetSame values index value bound]
    exact hvalue
  · rw [sliceSetNe values index value other same]
    apply hvalues other
    simpa [sliceSetLength] using hother

private theorem wrappingAddOneExact
    (index : Std.Usize) (bound : index.val < 16) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  have hsize : 17 < Usize.size := by
    have literalBound := (18#usize).hSize
    scalar_tac
  rw [Nat.mod_eq_of_lt]
  omega

structure ActiveTransition
    (alpha alpha2 alpha3 : RawQM31) (state : FoldState) : Type where
  scalesOut : Slice RawQM31
  xsOut : Slice RawM31
  scale : RawQM31
  x : RawM31
  scaleOut : RawQM31
  xOut : RawM31
  edge :
    sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
        alpha alpha2 alpha3 state.1 state.2.1 state.2.2 =
      ok (cont (scalesOut, xsOut,
        Std.Usize.wrapping_add state.2.2 1#usize))
  xCanonical : GeneratedCanonicalM31 xOut
  scaleCanonical : GeneratedCanonicalQM31 scaleOut
  scaleRaw : scale = state.1.val[state.2.2.val]!
  xRaw : x = state.2.1.val[state.2.2.val]!
  xExact : generatedM31ToExact xOut =
    doubledM31 (doubledM31 (generatedM31ToExact x))
  scaleExact : generatedQm31ToExact scaleOut =
    generatedQm31ToExact scale *
      lineBatchFoldNumerator (generatedQm31ToExact alpha)
        (generatedM31ToExact x)
  scalesSet : scalesOut = state.1.set state.2.2 scaleOut
  xsSet : xsOut = state.2.1.set state.2.2 xOut

set_option maxHeartbeats 500000 in
private theorem activeTransitionExists
    (alpha alpha2 alpha3 : RawQM31) (state : FoldState)
    (active : state.2.2 < Slice.len state.1)
    (sameLength : state.2.1.val.length = state.1.val.length)
    (currentScalesCanonical : CanonicalQM31Slice state.1)
    (currentXsCanonical : CanonicalM31Slice state.2.1)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3) :
    Nonempty (ActiveTransition alpha alpha2 alpha3 state) := by
  have scaleBound : state.2.2.val < state.1.val.length := by
    simpa [Slice.len_val] using active
  have xBound : state.2.2.val < state.2.1.val.length := by
    rw [sameLength]
    exact scaleBound
  obtain ⟨scale, scaleRead, scaleValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec state.1 state.2.2 scaleBound)
  obtain ⟨x, xRead, xValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec state.2.1 state.2.2 xBound)
  have scaleRaw : scale = state.1.val[state.2.2.val]! := by
    rw [scaleValue]
    symm
    apply List.getElem!_of_getElem?
    simp [scaleBound]
  have xRaw : x = state.2.1.val[state.2.2.val]! := by
    rw [xValue]
    symm
    apply List.getElem!_of_getElem?
    simp [xBound]
  have scaleCanonical : GeneratedCanonicalQM31 scale := by
    rw [scaleRaw]
    exact currentScalesCanonical state.2.2.val scaleBound
  have xCanonical : GeneratedCanonicalM31 x := by
    rw [xRaw]
    exact currentXsCanonical state.2.2.val xBound
  obtain ⟨step⟩ :=
    active_line_batch_fold_step_result state.1 state.2.1 state.2.2 scale x
      alpha alpha2 alpha3 active xBound scaleCanonical xCanonical halpha
      halpha2 halpha3 halpha2Exact halpha3Exact scaleRead xRead
  exact ⟨{
    scalesOut := step.scalesOut
    xsOut := step.xsOut
    scale := scale
    x := x
    scaleOut := step.scaleOut
    xOut := step.xOut
    edge := step.edge
    xCanonical := step.xCanonical
    scaleCanonical := step.scaleCanonical
    scaleRaw := scaleRaw
    xRaw := xRaw
    xExact := step.xExact
    scaleExact := step.scaleExact
    scalesSet := step.scalesSet
    xsSet := step.xsSet }⟩

private theorem transitionPreservesPrefix
    (baseScales : Slice RawQM31) (baseXs : Slice RawM31)
    (alpha alpha2 alpha3 : RawQM31) (state : FoldState)
    (invariant : FoldPrefix (generatedQm31ToExact alpha)
      baseScales baseXs state)
    (transition : ActiveTransition alpha alpha2 alpha3 state) :
    FoldPrefix (generatedQm31ToExact alpha) baseScales baseXs
      (transition.scalesOut, transition.xsOut,
        Std.Usize.wrapping_add state.2.2 1#usize) := by
  have activeBound : state.2.2.val < baseScales.val.length := by
    have edgeResult := transition.edge
    unfold
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body at edgeResult
    by_contra inactive
    have inactive' : ¬ state.2.2 < Slice.len state.1 := by
      intro active
      have activeVal : state.2.2.val < state.1.val.length := by
        simpa [Slice.len_val] using active
      rw [invariant.stateScalesLength] at activeVal
      exact inactive activeVal
    rw [if_neg inactive'] at edgeResult
    cases edgeResult
  have nextVal : (Std.Usize.wrapping_add state.2.2 1#usize).val =
      state.2.2.val + 1 := wrappingAddOneExact state.2.2
        (by rw [← invariant.baseLength]; exact activeBound)
  rw [transition.scalesSet, transition.xsSet]
  refine {
    stateScalesLength := ?_
    stateXsLength := ?_
    baseLengths := invariant.baseLengths
    baseLength := invariant.baseLength
    extentBound := ?_
    currentScalesCanonical := ?_
    currentXsCanonical := ?_
    processed := ?_
    untouched := ?_ }
  · rw [sliceSetLength, invariant.stateScalesLength]
  · rw [sliceSetLength, invariant.stateXsLength]
  · rw [nextVal]
    omega
  · exact canonicalQM31Set state.1 state.2.2 transition.scaleOut
      (by rw [invariant.stateScalesLength]; exact activeBound)
      invariant.currentScalesCanonical transition.scaleCanonical
  · exact canonicalM31Set state.2.1 state.2.2 transition.xOut
      (by rw [invariant.stateXsLength, invariant.baseLengths]; exact activeBound)
      invariant.currentXsCanonical transition.xCanonical
  · intro index indexBelow
    change generatedQm31ToExact
        (state.1.set state.2.2 transition.scaleOut).val[index]! =
          generatedQm31ToExact baseScales.val[index]! *
            lineBatchFoldNumerator (generatedQm31ToExact alpha)
              (generatedM31ToExact baseXs.val[index]!) ∧
      generatedM31ToExact
        (state.2.1.set state.2.2 transition.xOut).val[index]! =
          doubledM31 (doubledM31
            (generatedM31ToExact baseXs.val[index]!))
    rw [nextVal] at indexBelow
    by_cases same : index = state.2.2.val
    · subst index
      rw [sliceSetSame state.1 state.2.2 transition.scaleOut
          (by rw [invariant.stateScalesLength]; exact activeBound),
        sliceSetSame state.2.1 state.2.2 transition.xOut
          (by
            rw [invariant.stateXsLength, invariant.baseLengths]
            exact activeBound)]
      constructor
      · rw [transition.scaleExact, transition.scaleRaw, transition.xRaw]
        rw [(invariant.untouched state.2.2.val (by omega) activeBound).1,
          (invariant.untouched state.2.2.val (by omega) activeBound).2]
      · rw [transition.xExact, transition.xRaw]
        rw [(invariant.untouched state.2.2.val (by omega) activeBound).2]
    · have previous : index < state.2.2.val := by omega
      rw [sliceSetNe state.1 state.2.2 transition.scaleOut index same,
        sliceSetNe state.2.1 state.2.2 transition.xOut index same]
      exact invariant.processed index previous
  · intro index afterNext indexBound
    change (state.1.set state.2.2 transition.scaleOut).val[index]! =
        baseScales.val[index]! ∧
      (state.2.1.set state.2.2 transition.xOut).val[index]! =
        baseXs.val[index]!
    rw [nextVal] at afterNext
    have ne : index ≠ state.2.2.val := by omega
    rw [sliceSetNe state.1 state.2.2 transition.scaleOut index ne,
      sliceSetNe state.2.1 state.2.2 transition.xOut index ne]
    exact invariant.untouched index (by omega) indexBound

private theorem traceFinishesPrefix
    (baseScales : Slice RawQM31) (baseXs : Slice RawM31)
    (alpha alpha2 alpha3 : RawQM31)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3) :
    ∀ {state output},
      ExactLoopTrace
        (fun state : FoldState =>
          sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
            alpha alpha2 alpha3 state.1 state.2.1 state.2.2)
        state output →
      FoldPrefix (generatedQm31ToExact alpha) baseScales baseXs state →
      FoldPrefix (generatedQm31ToExact alpha) baseScales baseXs
        (output.1, output.2, 16#usize) := by
  intro state output execution
  induction execution with
  | @done current final edge =>
      intro invariant
      by_cases active : current.2.2 < Slice.len current.1
      · obtain ⟨transition⟩ := activeTransitionExists
          alpha alpha2 alpha3 current active
          (by rw [invariant.stateXsLength, invariant.baseLengths,
            ← invariant.stateScalesLength])
          invariant.currentScalesCanonical invariant.currentXsCanonical
          halpha halpha2 halpha3 halpha2Exact halpha3Exact
        have impossible := Result.ok.inj (edge.symm.trans transition.edge)
        cases impossible
      · have outputExact : final = (current.1, current.2.1) := by
          unfold
            sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body at edge
          rw [if_neg active] at edge
          exact ControlFlow.done.inj (Result.ok.inj edge) |>.symm
        subst final
        have finalInvariant := invariant
        have exhausted : current.2.2.val = 16 := by
          have notLess : ¬ current.2.2.val < 16 := by
            intro less
            apply active
            rw [UScalar.lt_equiv]
            simpa [Slice.len_val, invariant.stateScalesLength,
              invariant.baseLength] using less
          have atMost : current.2.2.val ≤ 16 := by
            rw [← invariant.baseLength]
            exact invariant.extentBound
          omega
        have finalIndex : (16#usize : Std.Usize) = current.2.2 := by
          apply UScalar.eq_of_val_eq
          exact exhausted.symm
        simpa [finalIndex] using finalInvariant
  | @cont current nextState final edge tail ih =>
      intro invariant
      have active : current.2.2 < Slice.len current.1 := by
        by_contra inactive
        unfold
          sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body at edge
        rw [if_neg inactive] at edge
        cases edge
      obtain ⟨transition⟩ := activeTransitionExists
        alpha alpha2 alpha3 current active
        (by rw [invariant.stateXsLength, invariant.baseLengths,
          ← invariant.stateScalesLength])
        invariant.currentScalesCanonical invariant.currentXsCanonical
        halpha halpha2 halpha3 halpha2Exact halpha3Exact
      have nextExact : nextState =
          (transition.scalesOut, transition.xsOut,
            Std.Usize.wrapping_add current.2.2 1#usize) := by
        exact ControlFlow.cont.inj (Result.ok.inj
          (edge.symm.trans transition.edge))
      subst nextState
      exact ih (transitionPreservesPrefix baseScales baseXs alpha alpha2 alpha3
        current invariant transition)

theorem fold_line_m31_batch_loop_exact
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (alpha alpha2 alpha3 : RawQM31)
    (lengthExact : scales.val.length = 16)
    (sameLength : xs.val.length = scales.val.length)
    (hscales : CanonicalQM31Slice scales)
    (hxs : CanonicalM31Slice xs)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop
        scales xs alpha alpha2 alpha3 0#usize = ok (scalesOut, xsOut)) :
    FoldPrefix (generatedQm31ToExact alpha) scales xs
      (scalesOut, xsOut, 16#usize) := by
  unfold sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop at run
  obtain ⟨execution⟩ := loop_success_yields_exact_trace
    (fun state : FoldState =>
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
        alpha alpha2 alpha3 state.1 state.2.1 state.2.2)
    (scales, xs, 0#usize) (scalesOut, xsOut) run
  have linePrefix : FoldPrefix (generatedQm31ToExact alpha) scales xs
      (scalesOut, xsOut, 16#usize) := by
    apply traceFinishesPrefix scales xs alpha alpha2 alpha3 halpha halpha2
      halpha3 halpha2Exact halpha3Exact execution
    refine {
      stateScalesLength := rfl
      stateXsLength := rfl
      baseLengths := sameLength
      baseLength := lengthExact
      extentBound := by norm_num
      currentScalesCanonical := hscales
      currentXsCanonical := hxs
      processed := ?_
      untouched := ?_ }
    · intro index impossible
      norm_num at impossible
    · intro index _ indexBound
      exact ⟨rfl, rfl⟩
  exact linePrefix

/-- Direct natural-number view of every entry produced by the completed loop.
This is proved from the local trace so consumers never project the dependent
field from an opaque `FoldPrefix` result. -/
theorem fold_line_m31_batch_loop_processed
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (alpha alpha2 alpha3 : RawQM31)
    (lengthExact : scales.val.length = 16)
    (sameLength : xs.val.length = scales.val.length)
    (hscales : CanonicalQM31Slice scales)
    (hxs : CanonicalM31Slice xs)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run :
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop
        scales xs alpha alpha2 alpha3 0#usize = ok (scalesOut, xsOut)) :
    ∀ position : Fin 16,
      LineEntryExact (generatedQm31ToExact alpha)
        scales xs scalesOut xsOut position.val := by
  unfold sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop at run
  obtain ⟨execution⟩ := loop_success_yields_exact_trace
    (fun state : FoldState =>
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
        alpha alpha2 alpha3 state.1 state.2.1 state.2.2)
    (scales, xs, 0#usize) (scalesOut, xsOut) run
  have linePrefix : FoldPrefix (generatedQm31ToExact alpha) scales xs
      (scalesOut, xsOut, 16#usize) := by
    apply traceFinishesPrefix scales xs alpha alpha2 alpha3 halpha halpha2
      halpha3 halpha2Exact halpha3Exact execution
    refine {
      stateScalesLength := rfl
      stateXsLength := rfl
      baseLengths := sameLength
      baseLength := lengthExact
      extentBound := by norm_num
      currentScalesCanonical := hscales
      currentXsCanonical := hxs
      processed := ?_
      untouched := ?_ }
    · intro index impossible
      norm_num at impossible
    · intro index _ indexBound
      exact ⟨rfl, rfl⟩
  intro position
  have facts := linePrefix.processed position.val (by
    simpa only [UScalar.ofNatCore_val_eq] using position.isLt)
  exact ⟨by simpa only [lineQM31At, lineM31At] using facts.1,
    by simpa only [lineQM31At, lineM31At] using facts.2⟩

#print axioms fold_line_m31_batch_loop_exact
#print axioms fold_line_m31_batch_loop_processed

end V7CallerCurrentReleaseR26LineBatchFoldLoop
