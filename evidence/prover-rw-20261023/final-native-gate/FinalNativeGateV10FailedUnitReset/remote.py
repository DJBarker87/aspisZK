import subprocess,os,json,time
UNIT='FinalNativeGate-pin-setup.scope'
EXPECTED='28bdad7bd8784522aba44fc8b4b9b45c'
ENV=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
SHOW=['/usr/bin/systemctl','--user','show',UNIT,'--property=Id,LoadState,ActiveState,SubState,InvocationID,ControlGroup']
def show():
 p=subprocess.run(SHOW,env=ENV,capture_output=True,timeout=5)
 if p.returncode or len(p.stdout)+len(p.stderr)>65536:raise ValueError('fixed status failed/bound')
 r=dict(x.split('=',1) for x in p.stdout.decode().splitlines())
 if set(r)!={'Id','LoadState','ActiveState','SubState','InvocationID','ControlGroup'} or r['Id']!=UNIT:raise ValueError('status fields')
 return r
start=time.monotonic();before=show();print(json.dumps(dict(phase='before',row=before)),flush=True)
if before['LoadState']=='not-found' and before['ActiveState']=='inactive' and before['ControlGroup']=='':
 print(json.dumps(dict(action='none',reason='already not-found/inactive; no failed state to clear',formal_calls=0)),flush=True)
else:
 expected=dict(Id=UNIT,LoadState='loaded',ActiveState='failed',SubState='failed',InvocationID=EXPECTED,ControlGroup='')
 if before!=expected:raise ValueError('failed unit identity/state changed; refuse reset')
 argv=['/usr/bin/systemctl','--user','reset-failed',UNIT]
 p=subprocess.run(argv,env=ENV,capture_output=True,timeout=5)
 if p.returncode or len(p.stdout)+len(p.stderr)>65536:raise ValueError('fixed reset failed/bound')
 print(json.dumps(dict(action=argv,exit=p.returncode,no_stop_or_signal=True)),flush=True)
 after=show();print(json.dumps(dict(phase='after',row=after,wall_seconds=time.monotonic()-start,formal_calls=0,claim='failed-unit metadata reset only; no kernel/orphan closure inferred')),flush=True)
 if after['LoadState']!='not-found' or after['ActiveState']!='inactive' or after['ControlGroup']!='':raise ValueError('post-reset not yet absent/inactive')
