import R1Z.CausalPremisesR1PBin
import R1Z.PrivacySimulatorBin

/-! Focused integration root: the premise reductions coexist with the binary
privacy/simulator root. Its source-refinement hypotheses remain explicit.
Existing privacy roots are unchanged; this is not a frozen-manifest replay. -/
#print axioms R1Z.PrivacySimulatorBin.privacy_R1_eff_binary
#print axioms R1Z.PremisesR1PBin.commit_bytes_iff
#print axioms R1Z.PremisesR1PBin.com_log_iff
#print axioms R1Z.PremisesR1PBin.root_causal_of_predecessors
#print axioms R1Z.PremisesR1PBin.open_of_batches
