import Lean
import NEP_WALKER
-- One private-data environment shared by both NDR-cohort roots.
run_cmd NEP.auditModules #[`RPx_Deployed, `NDR_CombinedAudit] #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDR_CombinedAudit.sourceOnHeadline] "NEP_Combined"
