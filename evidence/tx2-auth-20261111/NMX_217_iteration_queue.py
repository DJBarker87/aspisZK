from NMX_formal import *
for a,n,inverse in [('NMX_K015','NMX_assign_contract',False),('NMX_K016','NMX_assign_contract',True),('NMX_K017','NMX_guard_contract',False),('NMX_K018','NMX_guard_contract',True)]:
 h='r1_pool_adapter::NMX_217_native::iteration::'+n
 r=run(a,'kani',h,command=['python3','NMX_217_gate.py',a,h],extra={'NMX_217_gate.py':(E/'NMX_217_gate.py').read_text()},env_extra={'NMX_217_INVERSE':'1'} if inverse else {})
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if inverse:assert r['exit_status']==1 and 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log and ('NMX_assign_post' in log or 'NMX_guard_post' in log),'No intended semantic control failure'
 else:assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log, 'STOP failed positive predecessor'
