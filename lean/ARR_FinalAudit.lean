import ARR_OffPath
import ARR_FiniteFresh
import ARR_FreshState
import ARR_FactoryLoss
import ARR_OracleCoverage
import ARR_OracleLoss
import ARR_WorldCompatibility
import ARR_ReturnCoverage
import ARR_PrefixCost
import ARR_CoveredExamples
set_option autoImplicit false
#check @AspisR1.ARR_OracleCoverage.exact
#print axioms AspisR1.ARR_OracleCoverage.exact
#check @AspisR1.ARR_OracleCoverage.digest_iff
#print axioms AspisR1.ARR_OracleCoverage.digest_iff
#check @AspisR1.ARR_OracleLoss.digest_loss
#print axioms AspisR1.ARR_OracleLoss.digest_loss
#check @AspisR1.ARR_OracleLoss.cost_loss
#print axioms AspisR1.ARR_OracleLoss.cost_loss
#check @AspisR1.ARR_WorldCompatibility.iff_witness
#print axioms AspisR1.ARR_WorldCompatibility.iff_witness
#check @AspisR1.ARR_WorldCompatibility.separates
#print axioms AspisR1.ARR_WorldCompatibility.separates
#check @AspisR1.ARR_WorldCompatibility.not_all_worlds
#print axioms AspisR1.ARR_WorldCompatibility.not_all_worlds
#check @AspisR1.ARR_ReturnCoverage.of_returns
#print axioms AspisR1.ARR_ReturnCoverage.of_returns
#check @AspisR1.ARR_ReturnCoverage.returns_of_covered
#print axioms AspisR1.ARR_ReturnCoverage.returns_of_covered
#check @AspisR1.ARR_ReturnCoverage.iff_returns
#print axioms AspisR1.ARR_ReturnCoverage.iff_returns
#check @AspisR1.ARR_PrefixCost.suffix
#print axioms AspisR1.ARR_PrefixCost.suffix
#check @AspisR1.ARR_PrefixCost.native_le_ideal
#print axioms AspisR1.ARR_PrefixCost.native_le_ideal
#check @AspisR1.ARR_PrefixCost.same_cost_iff_empty
#print axioms AspisR1.ARR_PrefixCost.same_cost_iff_empty
#check @AspisR1.ARR_CoveredExamples.ideal_dictionary
#print axioms AspisR1.ARR_CoveredExamples.ideal_dictionary
#check @AspisR1.ARR_CoveredExamples.rejected
#print axioms AspisR1.ARR_CoveredExamples.rejected
#check @AspisR1.ARR_CoveredExamples.rejected_returns
#print axioms AspisR1.ARR_CoveredExamples.rejected_returns
#check @AspisR1.ARR_OffPath.different
#print axioms AspisR1.ARR_OffPath.different
#check @AspisR1.ARR_OffPath.change
#print axioms AspisR1.ARR_OffPath.change
#check @AspisR1.ARR_OffPath.incompatible_same_run
#print axioms AspisR1.ARR_OffPath.incompatible_same_run
#check @AspisR1.ARR_OffPath.factory_forces_reads
#print axioms AspisR1.ARR_OffPath.factory_forces_reads
#check @AspisR1.ARR_FiniteFresh.missing
#print axioms AspisR1.ARR_FiniteFresh.missing
#check @AspisR1.ARR_FreshState.flatten_parts
#print axioms AspisR1.ARR_FreshState.flatten_parts
#check @AspisR1.ARR_FreshState.fresh
#print axioms AspisR1.ARR_FreshState.fresh
#check @AspisR1.ARR_FreshState.no_factory
#print axioms AspisR1.ARR_FreshState.no_factory
#check @AspisR1.ARR_FactoryLoss.state_card
#print axioms AspisR1.ARR_FactoryLoss.state_card
#check @AspisR1.ARR_FactoryLoss.same_execution
#print axioms AspisR1.ARR_FactoryLoss.same_execution
#check @AspisR1.ARR_FactoryLoss.bounded_no_factory
#print axioms AspisR1.ARR_FactoryLoss.bounded_no_factory
