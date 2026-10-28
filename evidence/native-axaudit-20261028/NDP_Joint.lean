import Lean
import JHx_Joint
import NDP_Audit
set_option pp.all true
set_option pp.deepTerms true
run_cmd Lean.logInfo "NDP_POST_IMPORT"
#print axioms AspisR1.JHx_Joint.source
run_cmd NDP.audit `AspisR1.JHx_Joint.source "NDP_Joint"
