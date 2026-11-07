from NMX_formal import *
for a,n,expected in [('NMX_K008','NMX_shape_contract',0),('NMX_K009','NMX_shape_real',0),('NMX_K010','NMX_shape_stub',1),('NMX_K011','NMX_shape_modifies',1)]:
 h='r1_pool_adapter::NMX_217_native::fidelity::'+n
 r=run(a,'kani',h,command=['python3','NMX_217_gate.py',a,h],extra={'NMX_217_gate.py':(E/'NMX_217_gate.py').read_text()})
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if expected==1:
  assert 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log, 'STOP: nonsemantic failure is not a control verdict'
 if r['exit_status']!=expected:raise RuntimeError('STOP unexpected control verdict '+a)
