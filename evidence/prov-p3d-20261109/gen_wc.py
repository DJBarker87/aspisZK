import re,sys
sys.path.insert(0,'.')
import ext,gen_loops
blocks=open('/tmp/e002_blocks.txt').read().split('\n=====\n')
blocks=[re.sub(r'^@\[rust_loop(?:_body)?\]\n','',b,flags=re.M) for b in blocks]
gen_loops.GNAME.update({'atomic_statement.encode_digest_canonical_loop.body':'encode_digest_canonical_loop.body','atomic_statement.encode_digest_canonical_loop':'encode_digest_canonical_loop','atomic_statement.encode_digest_canonical':'encode_digest_canonical'})
F='AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs.'; G='AspisR1WithdrawalCaller.'
extra=f'''
set_option maxHeartbeats 200000 in
theorem PRVD.Eq.digest_version : {F}pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = {G}pool_v1.POOL_V1_DIGEST_ENCODING_VERSION := by
  delta {F}pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION {G}pool_v1.POOL_V1_DIGEST_ENCODING_VERSION
  rfl
#print axioms PRVD.Eq.digest_version
'''
res=ext.build('../prov-p3c-20261109/PRVEq_AspisR1WithdrawalCaller_Funs_P3.lean','PRVEq_AspisR1WithdrawalCaller_Funs_P3d.lean',
  undrop=['pool_v1.payment_relation.encode_common','pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1'],
  insert=blocks,insert_before='/-- [aspis_statement::pool_v1::payment_relation::encode_common]:',bridge=True,
  steps=[('nonloop','atomic_statement.encode_digest_canonical_loop.body'),('nonloop','atomic_statement.encode_digest_canonical_loop'),('nonloop','atomic_statement.encode_digest_canonical')],extra=extra)
s=open('PRVEq_AspisR1WithdrawalCaller_Funs_P3d.lean').read()
consts=re.findall(r'^theorem (PRVEq\.AspisR1WithdrawalCaller\.Funs\.pool_v1\.payment_relation\.[A-Z_0-9]+) :',s,re.M)
simp=', '.join(['PRVC.Eq.atomic_statement.encode_digest_canonical','PRVD.Eq.digest_version']+consts)
s+=f'''
set_option maxHeartbeats 400000 in
theorem PRVC.Eq.encode_common : @{F}pool_v1.payment_relation.encode_common = @{G}pool_v1.payment_relation.encode_common := by
  delta {F}pool_v1.payment_relation.encode_common {G}pool_v1.payment_relation.encode_common
  simp only [{simp}]
#print axioms PRVC.Eq.encode_common

set_option maxHeartbeats 400000 in
theorem PRVC.Eq.encode_pool_v1_withdrawal_public_v1 : @{F}pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 = @{G}pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 := by
  delta {F}pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 {G}pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
  simp only [PRVC.Eq.encode_common, PRVC.Eq.validate_pool_v1_withdrawal_public_v1, PRVEq.AspisR1WithdrawalCaller.Funs.pool_v1.payment_relation.withdrawal_common, PRVC.Eq.atomic_statement.encode_digest_canonical, {', '.join(consts)}]
  rfl
#print axioms PRVC.Eq.encode_pool_v1_withdrawal_public_v1
'''
open('PRVEq_AspisR1WithdrawalCaller_Funs_P3d.lean','w').write(s)
