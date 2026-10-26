import P6C_Accepted
import P6C_Batches
import P6C_Callbacks
import P6C_CarrierGap
import P6C_EventTransport
import P6C_Extension
import P6C_Forget
import P6C_FullBoundary
import P6C_Irrelevance
import P6C_Issued
import P6C_NativeEffects
import P6C_Nonvacuity
import P6C_OnCuts
import P6C_Pair
import P6C_Result
import P6C_Top
import P6C_Whole

-- Focused closure/statement audit only; no package replay.
#print axioms AspisR1.P6C_Accepted.issued_calls_ok
#print axioms AspisR1.P6C_Accepted.actual_calls_ok
#print axioms AspisR1.P6C_Accepted.extension_irrelevant
#print axioms AspisR1.P6C_Batches.current
#print axioms AspisR1.P6C_Batches.stage
#print axioms AspisR1.P6C_Batches.stage_native
#print axioms AspisR1.P6C_Callbacks.digest
#print axioms AspisR1.P6C_Callbacks.parent_trace
#print axioms AspisR1.P6C_Callbacks.parent_accepted
#print axioms AspisR1.P6C_Callbacks.leaf_trace
#print axioms AspisR1.P6C_Callbacks.leaf_accepted
#print axioms AspisR1.P6C_CarrierGap.independent
#print axioms AspisR1.P6C_EventTransport.inclusion
#print axioms AspisR1.P6C_EventTransport.mass
#print axioms AspisR1.P6C_Extension.agrees
#print axioms AspisR1.P6C_Extension.realization
#print axioms AspisR1.P6C_Extension.boundary
#print axioms AspisR1.P6C_Extension.source_preserved
#print axioms AspisR1.P6C_Forget.result
#print axioms AspisR1.P6C_FullBoundary.same_cuts
#print axioms AspisR1.P6C_Irrelevance.issued_only
#print axioms AspisR1.P6C_Irrelevance.conclusions
#print axioms AspisR1.P6C_Issued.derive
#print axioms AspisR1.P6C_Issued.installed
#print axioms AspisR1.P6C_Issued.parent
#print axioms AspisR1.P6C_NativeEffects.values_append
#print axioms AspisR1.P6C_NativeEffects.source
#print axioms AspisR1.P6C_NativeEffects.accepted
#print axioms AspisR1.P6C_NativeEffects.no_lost_calls
#print axioms AspisR1.P6C_Nonvacuity.partial_accepted
#print axioms AspisR1.P6C_Nonvacuity.rejected_differs
#print axioms AspisR1.P6C_OnCuts.same_cuts
#print axioms AspisR1.P6C_Pair.safe
#print axioms AspisR1.P6C_Pair.accepted_pair_calls
#print axioms AspisR1.P6C_Result.strengthen
#print axioms AspisR1.P6C_Top.deployed
#print axioms AspisR1.P6C_Whole.same_cuts
#print AspisR1.P6C_Extension.total
#print AspisR1.P6C_Extension.dictionary
#print AspisR1.P6C_Pair.Safe
#print AspisR1.P6C_OnCuts.SafeBatches
#print AspisR1.P6C_FullBoundary.Facts
#print AspisR1.P6C_Issued.Boundary
#print AspisR1.P6C_Result.Outcome
#check @AspisR1.Rc3_Top.deployed
#check @AspisR1.P6C_Top.deployed
