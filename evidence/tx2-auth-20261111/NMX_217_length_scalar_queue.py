from NMX_formal import *
h='r1_pool_adapter::NMX_217_native::NMX_217_all_lengths'
for a,inverse in [('NMX_K012',False),('NMX_K013',True)]:
 r=run(a,'kani',h,command=['python3','NMX_217_gate.py',a,h],extra={'NMX_217_gate.py':(E/'NMX_217_gate.py').read_text()},env_extra={'NMX_217_INVERSE':'1'} if inverse else {})
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if inverse:assert r['exit_status']==1 and 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log and 'n != 768' in log,'No expected semantic control failure'
 else:assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log
