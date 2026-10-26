import R1Z.PV_RunJoin_Source
import R1Z.PV_RunJoin_Coupling
import R1Z.PV_RunJoin_Endpoint

/-! Focused cached audit. This is not a full release dependency replay. -/
#print axioms R1Z.PV_RunJoin_Source.idleObserver
#print axioms R1Z.PV_RunJoin_Source.observer_nonempty
#print axioms R1Z.PV_RunJoin_Source.proof_accounts_entry
#print axioms R1Z.PV_RunJoin_Source.fixed_dictionary_obstruction
#print axioms R1Z.PV_RunJoin_Coupling.cp
#print axioms R1Z.PV_RunJoin_Coupling.real_marginal
#print axioms R1Z.PV_RunJoin_Coupling.model_marginal
#print axioms R1Z.PV_RunJoin_Coupling.completed_tape_mean
#print axioms R1Z.PV_RunJoin_Coupling.projection_cp
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.refinement_iff_view
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.complete_view_ext
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.complete_observer_pair_iff
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.runJoin
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.refinement_from_premises
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.privacy_headline_from_premises
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.uniform_V037
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.disclosed_V038
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.observerOracle_V038
