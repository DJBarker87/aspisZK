import NNH8_Statements
import TAS_FinalB
/-! L187 replay root. Not run 7's TAS_G0_COMBINED_IMPORT: only the TAS_FinalB closure is replayed, so this
root imports TAS_FinalB and the run-7 statement audit (NNH8_Statements, identical source). The module name is
kept so that the pinned run-7 NFX scanner binary (root `TAS_G0_COMBINED_IMPORT`, sha256 58cbfe20...) is used
unchanged. -/
#print axioms AspisR1.TAS_FinalB.deployed_splitB
#print axioms AspisR1.TAS_FinalB.deployed_charge
#print axioms AspisR1.TAS_FinalB.fail_sub_rec
#print axioms AspisR1.NNH8_DeployedOuter
