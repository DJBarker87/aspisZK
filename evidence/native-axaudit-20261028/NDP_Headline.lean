import Lean
import RPx_Deployed
import NDP_Audit
set_option pp.all true
set_option pp.deepTerms true
run_cmd Lean.Elab.Command.logInfo "NDP_POST_IMPORT"
#print axioms AspisR1.RPx_Deployed.deployed
run_cmd NDP.audit `AspisR1.RPx_Deployed.deployed "NDP_Headline"
