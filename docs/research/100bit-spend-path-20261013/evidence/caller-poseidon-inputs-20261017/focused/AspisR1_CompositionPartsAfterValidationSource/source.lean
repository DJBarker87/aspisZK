import AspisR1.PreparedCopyComposition
import CompositionPartsGatherStable

/-! Continue branch of the retained `composition_parts` caller, with its
Poseidon selector/oracle pair exposed as one callable parameter. The parameter
must later be instantiated with those exact source functions; this module does
not assert that source binding or entry-guard reachability. All other callees
are the already proved source cuts. No independent helper/index/variant values
are parameters of the caller. -/
set_option autoImplicit false
namespace AspisR1.CompositionPartsAfterValidation
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyEvaluateRowExact (QM Selectors)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Variant := AspisR1.CopyLinkWeightExact.Variant
abbrev Output := AspisR1.CompositionPartsTail.Output
abbrev Error := AspisR1.CompositionPartsTail.Error
abbrev PoseidonAt := Openings → Selectors → Result (Array QM 4#usize)

/-- Exact two-branch source `copy_variant` projection. -/
def copyVariant (v : pool_v1.pair_forest_semantic_terminal.CompiledVariant) : Variant :=
  match v with
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

def copyVariantSource (v : pool_v1.pair_forest_semantic_terminal.CompiledVariant) : Result Variant :=
  match v with
  | .PrivateTransfer => .ok .PrivateTransfer
  | .Withdrawal => .ok .Withdrawal

theorem copyVariantSource_success (v : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
    copyVariantSource v = .ok (copyVariant v) := by
  cases v <;> rfl

/-- The exact continue-branch call order: four gathers, same-point selectors,
Poseidon selector/oracle call, semantic evaluator, actual H1 selection, actual
variant projection, Copy evaluator with the public cursor, and the source tail.
The source tail is factored at its already proved exact post-Copy boundary. -/
def run (poseidonAt : PoseidonAt) (public1 : Public)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM) : Result (core.result.Result Output Error) := do
  let z ← array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO claims
  let succZ ← array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO claims
  let xorZ ← array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO claims
  let maskOnly ← array_from_fn_copy 10#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO claims
  let selectors ← pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
  let poseidon ← poseidonAt { z := z, succ_z := succZ, xor12_z := xorZ } selectors
  let semantic ← AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
    public1 { z := z, succ_z := succZ, xor12_z := xorZ } selectors
  let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  let helper ← pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i
  let variant ← copyVariantSource public1.variant
  let copy ← AspisR1.CopyEvaluatorFactor.evaluate z helper selectors lambda chi
    public1.transition.live_snapshot.next_pair_index variant
  AspisR1.CompositionPartsTail.run semantic poseidon theta copy.residual copy.active claims z maskOnly helper

#print axioms copyVariantSource_success
end AspisR1.CompositionPartsAfterValidation
