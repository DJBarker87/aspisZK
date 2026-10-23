import S9ActualPairScalarCallbackV1
import S9RangeFoldAcceptedTransportV1
import S9ActualPairFoldRunV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualPairScalarCallbackV1
namespace AspisR1S9ActualPairScalarFoldV1
local instance helperOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev SourceState := W × SC
abbrev HelperState := AspisR1S9HelperP6.field.WideExact × HC
abbrev R := core.ops.range.Range Usize

def mapState (s : SourceState) : HelperState := (toHelperW s.1,mapClosure s.2)
abbrev sourceCallback :=
  weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
abbrev helperCallback :=
  AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact

private theorem fold_step_eq_call {B F : Type}
    (callback : core.ops.function.FnMut F (B × Usize) B) (v : B) (c : F) (i : Usize) :
    AspisR1S9TransparentFoldRangeLawV1.foldStep callback (v,c) i = callback.call_mut c (v,i) := by
  unfold AspisR1S9TransparentFoldRangeLawV1.foldStep
  cases h : callback.call_mut c (v,i) with
  | fail e => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨v',c'⟩; rfl

/-- The same successful actual scalar fold state run maps to P6 and preserves
its read-only capture and canonical running accumulator, for every fuel/range.
The callback mapping and preservation facts are discharged by the actual
callback theorem, rather than retained as fold interface assumptions. -/
theorem scalar_range_run_success (fuel : Nat) (range : R)
    (c cout : SC) (initial out : W) (hp : GoodArray c.1) (hinit : Canonical initial)
    (h : AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range
      (AspisR1S9TransparentFoldRangeLawV1.foldStep sourceCallback) (initial,c) = .ok (out,cout)) :
    cout = c ∧ Canonical out ∧
      AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range
        (AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback) (mapState (initial,c)) =
          .ok (mapState (out,cout)) := by
  let inv : SourceState → Prop := fun state => state.2 = c ∧ Canonical state.1
  have hstep : ∀ state i next, inv state →
      AspisR1S9TransparentFoldRangeLawV1.foldStep sourceCallback state i = .ok next →
      inv next ∧ AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback (mapState state) i =
        .ok (mapState next) := by
    rintro ⟨acc,cap⟩ i ⟨value,capOut⟩ hi hs
    rcases hi with ⟨hcap,hacc⟩
    change cap = c at hcap
    change Canonical acc at hacc
    subst cap
    rw [fold_step_eq_call] at hs
    obtain ⟨hcapOut,hcan,hmodel⟩ := actual_callback_success_maps c capOut acc value i hp hacc hs
    refine ⟨⟨hcapOut,hcan⟩,?_⟩
    change AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback (toHelperW acc,mapClosure c) i =
      .ok (toHelperW value,mapClosure capOut)
    rw [fold_step_eq_call]
    exact hmodel
  have hjoined := AspisR1S9RangeFoldAcceptedTransportV1.range_fold_success_transport
    mapState inv (AspisR1S9TransparentFoldRangeLawV1.foldStep sourceCallback)
    (AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback) hstep
    fuel range (initial,c) (out,cout) ⟨rfl,hinit⟩ h
  exact ⟨hjoined.1.1,hjoined.1.2,hjoined.2⟩

#print axioms scalar_range_run_success
end AspisR1S9ActualPairScalarFoldV1
