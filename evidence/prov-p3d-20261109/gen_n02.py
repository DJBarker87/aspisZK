import sys,re
sys.path.insert(0,'.')
import ext
s=open('PRVEq_RPv_PoseidonPreparedSum3Source_P3d.lean').read()
m=re.search(r'(/-- \[aspis_core::field::qm31_sum_products3_prepared\]:.*?\ndef field.qm31_sum_products3_prepared\n.*?)\n\n',s,re.S)
blk=m.group(1)
ext.build('../prov-p3c-20261109/PRVEq_RPu_FIq_Native02_P3.lean','PRVEq_RPu_FIq_Native02_P3d.lean',insert=[blk],steps=[('loop','field.qm31_sum_products3_prepared_loop0_loop0_loop0'),('loop','field.qm31_sum_products3_prepared_loop0_loop0'),('loop','field.qm31_sum_products3_prepared_loop0'),('simp','field.qm31_sum_products3_prepared')])
