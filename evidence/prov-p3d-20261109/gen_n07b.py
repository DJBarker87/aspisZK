import sys
sys.path.insert(0,'.')
import ext,gen_p3
P='pool_v1.pair_forest_semantic_terminal.'
C='state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS'
ns='FIq_Native.PRVFresh_RPu_FIq_Native07.'
gen_p3.SHIMNAMES[:]=[ns+C,ns+'field.QM31.ZERO']
shim=f"/-- PCVD constant binding: the cross-crate fresh emission types this constant as `Result`; interpretation `ok <gate constant>`. -/\ndef {C} : Result Std.Usize := ok FIq_Native.{C}"
ext.build('PRVEq_RPu_FIq_Native07_P3.lean','PRVEq_RPu_FIq_Native07_P3b.lean',
  undrop=[P+'POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1',P+'selected_claim'],
  insert=[shim],insert_before='/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1]',
  steps=[('nonloop',P+'POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1'),('nonloop',P+'selected_claim')])
