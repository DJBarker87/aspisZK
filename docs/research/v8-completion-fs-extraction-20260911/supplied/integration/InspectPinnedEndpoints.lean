/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import SuccessfulCompleteSelectedWire
import SelectedResidualRecoveryBound
import SelectedResidualPrefixClassification

/-! Signature inspection of the READ remote pin only. This is not a repair
or integration proof. Add the user's completed local repair producer after
reconciling its exact module, signature and source hash. -/
set_option pp.all true in
#print AspisV8.SuccessfulCompleteSelectedWire.successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure
#print axioms AspisV8.SuccessfulCompleteSelectedWire.successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure

set_option pp.all true in
#print AspisV8.SelectedResidualRecoveryBound.conditional_nonpair_bound
#print axioms AspisV8.SelectedResidualRecoveryBound.conditional_nonpair_bound

set_option pp.all true in
#print AspisV8.SelectedResidualPrefixClassification.exists_source_classifier
#print axioms AspisV8.SelectedResidualPrefixClassification.exists_source_classifier
