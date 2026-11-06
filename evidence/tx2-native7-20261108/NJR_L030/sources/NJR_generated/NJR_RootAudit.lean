import NJJ_Common
import NJJ_DomainAudit
import NJF_Root
import NJR_FinishDomain
import NJR_ReservationRaw
import NJR_FinishAtSourceView
set_option autoImplicit false
/- Audit only: no positive TX2:065 theorem is declared. The following complete
statements expose the actual remaining History and native cut obligations. -/
#print NJJ_Common.run
#print NJR_FinishAtSourceView.at_source_view
#print NJJ_DomainAudit.public_lengths
#print AspisR1.NJF_Root.finish
#print NIG_FinishInput.Domain
#print axioms AspisR1.NJF_Root.finish
#print axioms AspisR1.RPx_Deployed.deployed
