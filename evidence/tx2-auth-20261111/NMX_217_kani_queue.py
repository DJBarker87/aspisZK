from NMX_formal import *
h='r1_pool_adapter::NMX_217_native::NMX_217_wrong_length'
for a,inverse in [('NMX_K001',False),('NMX_K002',True)]:
 env={'NMX_217_INVERSE':'1'} if inverse else {}
 r=run(a,'kani',h,command=['python3','NMX_217_gate.py',a,h],extra={'NMX_217_gate.py':(E/'NMX_217_gate.py').read_text()},env_extra=env)
 if (not inverse and r['exit_status']!=0) or (inverse and r['exit_status']==0):raise RuntimeError('Unexpected native verdict; stop queue')
