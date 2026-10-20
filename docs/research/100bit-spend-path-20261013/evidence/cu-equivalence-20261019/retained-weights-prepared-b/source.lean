import CuSavingsRetainedCompositionWeightsInputs
import CuSavingsRetainedPreparationInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionWeightsPrepared
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedCompositionWeightsInputs
variable [AspisR1S2Groups.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
  [AspisR1CuRho.ScalarKBlocks]

/-- Exact complete preparation prefix, followed by its unchanged consumer
context. The S2 continuation receives the actual immutable prepared values;
other variants retain the same fallback. No origin/canonicality field exists. -/
def sourceContext {State Output : Type} (common : PreparedCommon) (prefixCommon : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize)
    (block : verifier.Prepared → State → Result (core.result.Result Output verifier.Error))
    (context : verifier.Prepared → Array aspis_core.field.WideExact 29#usize →
      (State → Result (core.result.Result Output verifier.Error)) → Result (core.result.Result Output verifier.Error))
    (fallback : verifier.Prepared → Array aspis_core.field.WideExact 29#usize → Result (core.result.Result Output verifier.Error)) :
    Result (core.result.Result Output verifier.Error) :=
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefixCommon R B
  do
  let (prepared,gamma) ← retained.tx1_prepare D pub v hash obs initial
  match prepared with
  | .Err error => .ok (.Err error)
  | .Ok (_,p) =>
    match v.variant with
    | .S2 => context p gamma (block p)
    | _ => fallback p gamma

/-- The semantic verifier and actual scalar/power preparation supply every
input condition of the jointly replaced inactive/Libra block. The theorem
exposes no successful-child or canonical-source-input premise. Arbitrary
unchanged consumer contexts may fail, diverge or defer the block execution. -/
theorem source_context_equivalence {State Output : Type}
    (common : PreparedCommon) (prefixCommon : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize)
    (weights : State → AspisR1S2Groups.Weights)
    (after : verifier.Prepared → State → Low → GroupE → Parts → Result (core.result.Result Output verifier.Error))
    (context : verifier.Prepared → Array aspis_core.field.WideExact 29#usize →
      (State → Result (core.result.Result Output verifier.Error)) → Result (core.result.Result Output verifier.Error))
    (fallback : verifier.Prepared → Array aspis_core.field.WideExact 29#usize → Result (core.result.Result Output verifier.Error)) :
    sourceContext common prefixCommon R B D pub v hash obs initial
      (fun p => pair (blockNew weights v.final_message (after p)) p) context fallback =
      sourceContext common prefixCommon R B D pub v hash obs initial
        (fun p => pair (blockOld weights v.final_message (after p)) p) context fallback := by
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefixCommon R B
  unfold sourceContext
  apply (bind_eq_iff (retained.tx1_prepare D pub v hash obs initial) _ _).mpr
  intro prepared hprepared
  rcases prepared with ⟨result,gamma⟩
  simp only [uncurry_apply_pair]
  cases result with
  | Err error => rfl
  | Ok result =>
    rcases result with ⟨claims,p⟩
    cases hv : v.variant with
    | S1 => rfl
    | D => rfl
    | S2 =>
      have hf : transport.Variant.folds v.variant=.ok 2#usize := by
        rw [hv]
        simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
          transport.Variant.read_discriminant]
      obtain ⟨halpha,_,hsemantic⟩ := CuSavingsRetainedPreparationInputs.preparation_inputs
        common prefixCommon R B D pub v hash obs initial gamma claims p hprepared hf
      apply congrArg (context p gamma)
      funext state
      exact pair_equivalence weights v.final_message (after p) p halpha hsemantic state

#print axioms source_context_equivalence
end AspisR1.CuSavingsRetainedCompositionWeightsPrepared
