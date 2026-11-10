import sys
sys.path.insert(0,'.')
import ext,gen_loops
C='field.qm31_from_karatsuba_channel_sums'
callees=['field.P','field.reduce_u64','field.M31.add','field.M31.sub','field.M31.reduce_u64','field.M31.double','field.CM31.add','field.CM31.sub','field.mul_by_r']
for n in callees: gen_loops.GNAME[n]='!AspisR1SelectedMaskProbe.'+n
L='field.qm31_sum_products3_prepared'
ext.build('../prov-p2g-20261109/PRVEq_RPv_PoseidonPreparedSum3Source.lean','PRVEq_RPv_PoseidonPreparedSum3Source_P3d.lean',bridge=True,
  steps=[('nonloop',n) for n in callees]
        +[('simp',C+'.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call'),('simp',C),
          ('loop',L+'_loop0_loop0_loop0'),('loop',L+'_loop0_loop0'),('loop',L+'_loop0'),('simp',L)])
