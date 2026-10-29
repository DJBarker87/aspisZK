import PV_MEAS_Axioms
/-! Final frozen import-manifest consumer. Run once, after focused stages,
statement audit, and axioms audit are green. -/
set_option autoImplicit false
#check PV_MEAS_Deployed.privacy_headline_deployed_events_meas
#check PV_MEAS_Legacy.finite_uniform_corollary
#check PV_MEAS_Satisfiability.simultaneously_satisfiable
#print axioms PV_MEAS_Deployed.privacy_headline_deployed_events_meas
#print axioms PV_MEAS_Legacy.finite_uniform_corollary
#print axioms PV_MEAS_Satisfiability.simultaneously_satisfiable
