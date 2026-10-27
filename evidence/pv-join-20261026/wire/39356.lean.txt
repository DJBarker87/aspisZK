import R1Z.PV_Join_Wire_Dictionary
import R1Z.PV_Join_ProofClosure
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Caller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
abbrev native := PV_Join_Wire_Selection.native
-- Organisation of proved source laws, not discharge of the reservation or data equation.
theorem refinement_of_data (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    letI : ExternalTypes := native base
    ∀ {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)),
    data (ProverRwBodyNativeWideInstall.execute (PV_Join_Wire_Selection.selected base ops) store pub compiled v hash binding digest attempt s)=model →
      ProverRwBodyNativeWideInstall.execute (PV_Join_Wire_Selection.selected base ops) store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  letI : ExternalTypes := native base
  intro S store pub compiled v hash binding digest attempt s after accepted reservation model same
  rw [PV_Join_Wire_Dictionary.dictionary] at same ⊢
  apply eq_of_data after
  · exact ProverRwBodyReservationTransport.body_writeback
      (PV_Join_Wire_Dictionary.raw base ops) store pub compiled v hash
      binding digest attempt s after accepted reservation
  · exact ProverRwBodyCandidateData.keeps_withState after model
  · rw [ProverRwBodyCandidateData.data_withState]
    exact same
#print refinement_of_data
#print axioms refinement_of_data
end R1Z.PV_Join_Wire_Caller
#join_closure R1Z.PV_Join_AggregateCaller.refinement_of_data
#join_closure R1Z.PV_Join_Wire_Caller.refinement_of_data

namespace R1Z.PV_Join_Wire_Reachability
open Lean Elab Command
/-- Read-only declaration graph check: no theorem or trusted implementation. -/
elab "#wire_require " root:ident laws:str : command => do
  let env ← getEnv
  let mut todo := #[root.getId]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet.toArray do
          let text := dep.toString
          if text.startsWith "R1Z." || text.startsWith "_private.R1Z." then
            todo := todo.push dep
  let expected := laws.getString.splitOn ","
  for law in expected do
    unless seen.contains law.toName do
      throwError "WIRE MISSING: {law} from {root.getId}"
  logInfo m!"WIRE VERIFIED {expected.length} source laws in declaration closure of {root.getId}"
end R1Z.PV_Join_Wire_Reachability
#wire_require R1Z.PV_Join_Wire_Caller.refinement_of_data "R1Z.PV_CB_TakeSource.op3_source,R1Z.PV_CB_Op71Exact.op71_source,R1Z.PV_CB_Op72Exact.op72_source,R1Z.PV_CB_Op77Source.op77_source,R1Z.PV_CB_Op80Exact.op80_source,R1Z.PV_CB_Op82Source.op82_source,R1Z.PV_CB_Op83Source.op83_source,R1Z.PV_CB_Op84Exact.op84_source,R1Z.PV_CB_Op86Source.op86_source,R1Z.PV_CB_Op100Exact.op100_source,R1Z.PV_CB_Op101Exact.op101_source,R1Z.PV_CB_Op105Exact.op105_source,R1Z.PV_CB_Op107Exact.op107_source,R1Z.PV_CB_Op109Exact.op109_source,R1Z.PV_CB_Op110Source.op110_source,R1Z.PV_CB_Op111Source.op111_source,R1Z.PV_CB_Op114Source.op114_source,R1Z.PV_CB_Op118Exact.op118_source,R1Z.PV_CB3_Op120Source.op120_source,R1Z.PV_CB_Op127Source.op127_source,R1Z.PV_CB_Op128Source.op128_source,R1Z.PV_CB_Op130Source.op130_source,R1Z.PV_CB_Op131Source.op131_source,R1Z.PV_CB3_Op225Source.op225_source,R1Z.PV_CB_Op229Source.op229_source,R1Z.PV_CB3_Op246Source.op246_source,R1Z.PV_CB3_Op51Arbitrary.op51_source"
