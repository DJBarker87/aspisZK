import sys
sys.path.insert(0,'.')
import ext,gen_loops
gen_loops.GNAME['field.M31.reduce_u64']='!AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64'
alias="/- PRVE name-map alias: fresh type field.M31 (crate aspis_core, emitted without the crate prefix) is the gate type aspis_core.field.M31 -/\nabbrev field.M31 := AspisR1BatchedWeightsExtraction.aspis_core.field.M31"
ext.build('../prov-p2g-20261109/PRVEq_AspisR1BatchedWeightsExtraction_Funs.lean','PRVEq_AspisR1BatchedWeightsExtraction_Funs_P3d.lean',
  undrop=['field.M31.reduce_u64'],insert=[alias],insert_before='/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:',
  steps=[('nonloop','field.M31.reduce_u64')])
