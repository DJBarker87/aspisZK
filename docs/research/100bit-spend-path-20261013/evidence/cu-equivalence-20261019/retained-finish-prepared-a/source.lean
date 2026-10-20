import CuSavingsRetainedFinishTransport
import CuSavingsRetainedPreparationInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFinishPrepared
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared] [AspisR1CuRho.ScalarKBlocks]

theorem prepared_finish_equivalence {State : Type} (finish : CuSavingsRetainedFinishRelation.Boundaries State)
    (common : PreparedCommon) (prefix : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial final : Array aspis_core.field.WideExact 29#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) (p : verifier.Prepared)
    (h : letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
         letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefix R B
         retained.tx1_prepare D pub v hash obs initial=.ok (.Ok (claims,p),final))
    (a : AspisR1RhoTransactions.verifier.Accumulator) :
    CuSavingsRetainedFinishBinding.sourceFinish true finish (CuSavingsRetainedCompositionTx1Transport.view v)
      (CuSavingsRhoEntryTransport.prepared p) a obs =
    CuSavingsRetainedFinishBinding.sourceFinish false finish (CuSavingsRetainedCompositionTx1Transport.view v)
      (CuSavingsRhoEntryTransport.prepared p) a obs := by
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefix R B
  obtain ⟨sem,_,hp⟩ := CuSavingsRetainedCompositionTx1.preparation_origins D pub v hash obs initial final claims p h
  have hv := (CuSavingsRetainedSamplerPrepared.source_success common D sem v hash initial final p hp).2.1
  cases hvar : p.variant with
  | S1 => simp only [CuSavingsRetainedFinishBinding.sourceFinish,CuSavingsRhoEntryTransport.prepared,hvar]
  | D => simp only [CuSavingsRetainedFinishBinding.sourceFinish,CuSavingsRhoEntryTransport.prepared,hvar]
  | S2 =>
    have hf : transport.Variant.folds v.variant=.ok 2#usize := by
      rw [←hv,hvar]
      simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
    obtain ⟨ha,_,hc⟩ := CuSavingsRetainedPreparationInputs.preparation_inputs common prefix R B D pub v hash obs initial final claims p h hf
    obtain ⟨ha,hc⟩ := CuSavingsRetainedFinishTransport.inputs p ha hc
    exact CuSavingsRetainedFinishBinding.source_equivalence finish _ _ a obs ha hc

def run {State : Type} (newer : Bool) (finish : CuSavingsRetainedFinishRelation.Boundaries State)
    (tx : AspisR1RhoTransactions.TxCommon) (common : PreparedCommon) (prefix : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize)
    (work : AspisR1RhoTransactions.verifier.Prepared → Array aspis_core.field.WideExact 29#usize →
      Result (AspisR1RhoTransactions.core.result.Result AspisR1RhoTransactions.verifier.Accumulator AspisR1RhoTransactions.verifier.Error)) :
    Result (core.result.Result Unit verifier.Error) :=
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefix R B
  letI : AspisR1RhoTransactions.TxCommon := CuSavingsRetainedFinishBinding.binding newer finish tx
  do
  let (prepared,gamma) ← retained.tx1_prepare D pub v hash obs initial
  match prepared with
  | .Err error => .ok (.Err error)
  | .Ok (_,p) =>
    let result ← work (CuSavingsRhoEntryTransport.prepared p) gamma
    match result with
    | .Err error => .ok (.Err (CuSavingsRetainedCompositionTx1Transport.error error))
    | .Ok updated =>
      let result ← AspisR1RhoTransactions.finish_relation (CuSavingsRetainedCompositionTx1Transport.view v)
        (CuSavingsRhoEntryTransport.prepared p) updated obs
      .ok (CuSavingsRetainedCompositionTx1Transport.returned result)

theorem source_equivalence {State : Type} (finish : CuSavingsRetainedFinishRelation.Boundaries State)
    (tx : AspisR1RhoTransactions.TxCommon) (common : PreparedCommon) (prefix : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize)
    (work : AspisR1RhoTransactions.verifier.Prepared → Array aspis_core.field.WideExact 29#usize →
      Result (AspisR1RhoTransactions.core.result.Result AspisR1RhoTransactions.verifier.Accumulator AspisR1RhoTransactions.verifier.Error)) :
    run true finish tx common prefix R B D pub v hash obs initial work=
    run false finish tx common prefix R B D pub v hash obs initial work := by
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefix R B
  unfold run
  apply (bind_eq_iff (retained.tx1_prepare D pub v hash obs initial) _ _).mpr
  intro prepared hp
  rcases prepared with ⟨result,gamma⟩
  simp only [uncurry_apply_pair]
  cases result with
  | Err error => rfl
  | Ok result =>
    rcases result with ⟨claims,p⟩
    apply (bind_eq_iff (work (CuSavingsRhoEntryTransport.prepared p) gamma) _ _).mpr
    intro result hw
    cases result with
    | Err error => rfl
    | Ok updated =>
      have he := prepared_finish_equivalence finish common prefix R B D pub v hash obs initial gamma claims p hp updated
      change (do let r ← CuSavingsRetainedFinishBinding.sourceFinish true finish _ _ _ _; .ok (CuSavingsRetainedCompositionTx1Transport.returned r)) = _
      rw [he]
      rfl

#print axioms prepared_finish_equivalence
#print axioms source_equivalence
end AspisR1.CuSavingsRetainedFinishPrepared
