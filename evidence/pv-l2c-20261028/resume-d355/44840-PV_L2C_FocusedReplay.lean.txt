import PV_L2C_CombinedAudit
import PV_L2C_FixtureAudit
/-! Single final focused manifest: local laws, exact carrier, replay aliases. -/
set_option autoImplicit false
namespace PV_L2C_FocusedReplay
/-- A raw padding-table law, not a whole honest-native execution theorem. -/
def padding := @PV_L2C_PaddingNative.guard_outcomes
#print axioms padding
/-- The actual extracted scalar parser on canonical encoded words. -/
def parser := @PV_L2C_CanonicalParser.scalar_parse
#print axioms parser
/-- The actual extracted Q-add fold, retaining its explicit zero-sum premise. -/
def helper_fold := @PV_L2C_ExtractedFold.zero_sum
#print axioms helper_fold
/-- Both original fixtures satisfy precisely the requested honesty predicate. -/
def fixtures := PV_L2C_FixtureAudit.concrete
#print axioms fixtures
end PV_L2C_FocusedReplay
