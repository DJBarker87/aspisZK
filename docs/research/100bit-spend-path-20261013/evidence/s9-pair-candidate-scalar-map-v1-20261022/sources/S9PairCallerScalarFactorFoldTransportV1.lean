import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9HelperP6.Funs
import S9PairCallerStepOperationBridgeV1
import S9CandidateFoldMapPrimitivesV1
import S9PairCallerScalarFactorCallbackTransportV1
import TransparentFoldRangeLawV1
import RangeFoldP6ModelV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerScalarFactorFoldTransportV1

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapResult f

abbrev CQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PairClosure := AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure
abbrev P6Closure := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure

open AspisR1S9PairCallerStepV1

abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev mapPairClosure := AspisR1S9PairCallerScalarFactorCallbackTransportV1.mapPairClosure

def mapPairState (s : CW × PairClosure) : PW × P6Closure :=
  (toP6W s.1, mapPairClosure s.2)

/-- The pair caller scalar-factor fold, including all four generated FnMut
calls, maps to the retained P6 operation fold with the same returned result.
Both fail and divergence branches are preserved by the generic fold map. -/
theorem pair_scalar_factor_maps_to_p6
    (f : Array CQ (4#usize)) (p : Array CW (4#usize)) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult toP6W
      (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor f p) =
    @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray toP6Q f) (mapArray toP6W p) := by
  let callback :=
    AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
  let callbackP6 :=
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
  have hstep : ∀ s i,
      AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapPairState
        (AspisR1S9TransparentFoldRangeLawV1.foldStep callback s i) =
      AspisR1S9TransparentFoldRangeLawV1.foldStep callbackP6
        (mapPairState s) i := by
    intro s i
    rcases s with ⟨v,c⟩
    change AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapPairState
      (do
        let pair ←
          AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
            c (v,i)
        ok pair) =
      (do
        let pair ←
          AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
            (mapPairClosure c) (toP6W v,i)
        ok pair)
    have hcall := AspisR1S9PairCallerScalarFactorCallbackTransportV1.pair_call_mut_maps c v i
    change AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapPairState
      (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        c (v,i)) =
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        (mapPairClosure c) (toP6W v,i) at hcall
    exact AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (f := mapPairState) (g := mapPairState)
      (r := AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        c (v,i))
      (r' := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        (mapPairClosure c) (toP6W v,i))
      (k := fun z => ok z) (k' := fun z => ok z)
      hcall (by intro z; rfl)
  have hfold := AspisR1S9CandidateFoldMapPrimitivesV1.rangeFoldRun_map
    mapPairState
    (AspisR1S9TransparentFoldRangeLawV1.foldStep callback)
    (AspisR1S9TransparentFoldRangeLawV1.foldStep callbackP6)
    hstep 4 ({ start := 0#usize, «end» := 4#usize })
    (AspisR1S9PairCallerStepV1.field.WideExact.ZERO, (p, f))
  have hinit : mapPairState
      (AspisR1S9PairCallerStepV1.field.WideExact.ZERO, (p,f)) =
      (AspisR1S9HelperP6.field.WideExact.ZERO, (mapArray toP6W p, mapArray toP6Q f)) := by
    dsimp only [mapPairState, mapPairClosure,
      AspisR1S9PairCallerScalarFactorCallbackTransportV1.mapPairClosure]
    unfold AspisR1S9PairCallerStepV1.field.WideExact.ZERO
      AspisR1S9HelperP6.field.WideExact.ZERO
      AspisR1S9PairCallerStepV1.toP6W AspisR1S9PairCallerStepV1.toP6Q
      AspisR1S9PairCallerStepV1.toP6CM AspisR1S9PairCallerStepV1.toP6M
    unfold AspisR1S9PairCallerStepV1.field.QM31.ZERO
      AspisR1S9HelperP6.field.QM31.ZERO
      mapArray
    rfl
  rw [hinit] at hfold
  have hfoldCandidate :
      AspisR1S9PairCallerStepV1.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callback ({ start := 0#usize, «end» := 4#usize })
        AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f) =
      (do
        let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4
          ({ start := 0#usize, «end» := 4#usize })
          (AspisR1S9TransparentFoldRangeLawV1.foldStep callback)
          (AspisR1S9PairCallerStepV1.field.WideExact.ZERO, (p, f))
        ok value) := by
    have hsame :
        AspisR1S9PairCallerStepV1.core.iter.traits.iterator.Iterator.fold.default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          callback ({ start := 0#usize, «end» := 4#usize })
          AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f) =
        AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          callback ({ start := 0#usize, «end» := 4#usize })
          AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f) := by rfl
    rw [hsame]
    exact AspisR1S9TransparentFoldRangeLawV1.extracted_fold_eq_rangeFoldRun
      (callback := callback) _ _ _
  have hfoldP6 :
      @AspisR1S9HelperP6.FieldOps.iterFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callbackP6 ({ start := 0#usize, «end» := 4#usize })
        AspisR1S9HelperP6.field.WideExact.ZERO
        (mapArray toP6W p, mapArray toP6Q f) =
      (do
        let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4
          ({ start := 0#usize, «end» := 4#usize })
          (AspisR1S9TransparentFoldRangeLawV1.foldStep callbackP6)
          (AspisR1S9HelperP6.field.WideExact.ZERO,
            (mapArray toP6W p, mapArray toP6Q f))
        ok value) := by
    change AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callbackP6 ({ start := 0#usize, «end» := 4#usize })
        AspisR1S9HelperP6.field.WideExact.ZERO
        (mapArray toP6W p, mapArray toP6Q f) = _
    exact AspisR1S9TransparentFoldRangeLawV1.extracted_fold_eq_rangeFoldRun
      (callback := callbackP6) _ _ _
  have hmappedFold :
      AspisR1S9CandidateFoldMapPrimitivesV1.mapResult toP6W
        (AspisR1S9PairCallerStepV1.core.iter.traits.iterator.Iterator.fold.default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          callback ({ start := 0#usize, «end» := 4#usize })
          AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f)) =
      @AspisR1S9HelperP6.FieldOps.iterFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callbackP6 ({ start := 0#usize, «end» := 4#usize })
        AspisR1S9HelperP6.field.WideExact.ZERO
        (mapArray toP6W p, mapArray toP6Q f) := by
    rw [hfoldCandidate, hfoldP6]
    change AspisR1S9CandidateFoldMapPrimitivesV1.mapResult toP6W
      (do
        let state ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4
          ({ start := 0#usize, «end» := 4#usize })
          (AspisR1S9TransparentFoldRangeLawV1.foldStep callback)
          (AspisR1S9PairCallerStepV1.field.WideExact.ZERO, (p, f))
        ok state.1) =
      (do
        let state ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4
          ({ start := 0#usize, «end» := 4#usize })
          (AspisR1S9TransparentFoldRangeLawV1.foldStep callbackP6)
          (AspisR1S9HelperP6.field.WideExact.ZERO,
            (mapArray toP6W p, mapArray toP6Q f))
        ok state.1)
    exact AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (f := toP6W) (g := mapPairState)
      (r := AspisR1S3S9RangeFoldP6.rangeFoldRun 4
        ({ start := 0#usize, «end» := 4#usize })
        (AspisR1S9TransparentFoldRangeLawV1.foldStep callback)
        (AspisR1S9PairCallerStepV1.field.WideExact.ZERO, (p, f)))
      (r' := AspisR1S3S9RangeFoldP6.rangeFoldRun 4
        ({ start := 0#usize, «end» := 4#usize })
        (AspisR1S9TransparentFoldRangeLawV1.foldStep callbackP6)
        (AspisR1S9HelperP6.field.WideExact.ZERO,
          (mapArray toP6W p, mapArray toP6Q f)))
      (k := fun s => ok s.1) (k' := fun s => ok s.1)
      hfold (by intro s; cases s with | mk v c => rfl)
  unfold AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
    AspisR1S9HelperP6.weights.Weights.scalar_factor
  change AspisR1S9CandidateFoldMapPrimitivesV1.mapResult toP6W
      (do
        let we ← AspisR1S9PairCallerStepV1.core.iter.traits.iterator.Iterator.fold.default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
          ({ start := 0#usize, «end» := 4#usize })
          AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f)
        AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we
          AspisR1S9PairCallerStepV1.weights.QUARTER) =
    (do
      let we ← @AspisR1S9HelperP6.FieldOps.iterFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        ({ start := 0#usize, «end» := 4#usize })
        AspisR1S9HelperP6.field.WideExact.ZERO
        (mapArray toP6W p, mapArray toP6Q f)
      @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we AspisR1S9HelperP6.weights.QUARTER)
  exact AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (f := toP6W) (g := toP6W)
    (r := AspisR1S9PairCallerStepV1.core.iter.traits.iterator.Iterator.fold.default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      ({ start := 0#usize, «end» := 4#usize })
      AspisR1S9PairCallerStepV1.field.WideExact.ZERO (p, f))
    (r' := @AspisR1S9HelperP6.FieldOps.iterFold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      ({ start := 0#usize, «end» := 4#usize })
      AspisR1S9HelperP6.field.WideExact.ZERO
      (mapArray toP6W p, mapArray toP6Q f))
    (k := fun we => AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we
      AspisR1S9PairCallerStepV1.weights.QUARTER)
    (k' := fun we => @AspisR1S9HelperP6.FieldOps.wideMulM31
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we
      AspisR1S9HelperP6.weights.QUARTER)
    hmappedFold (by
      intro we
      have hquarter : AspisR1S9PairCallerStepV1.toP6M
          AspisR1S9PairCallerStepV1.weights.QUARTER =
          AspisR1S9HelperP6.weights.QUARTER := by
        unfold AspisR1S9PairCallerStepV1.weights.QUARTER
          AspisR1S9HelperP6.weights.QUARTER AspisR1S9PairCallerStepV1.toP6M
        rfl
      have hm := AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_m31 we
        AspisR1S9PairCallerStepV1.weights.QUARTER
      change AspisR1S9PairCallerStepOperationBridgeV1.mapResult toP6W
        (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we
          AspisR1S9PairCallerStepV1.weights.QUARTER) = _
      rw [← hquarter]
      exact hm)

#print axioms pair_scalar_factor_maps_to_p6

end AspisR1S9PairCallerScalarFactorFoldTransportV1
