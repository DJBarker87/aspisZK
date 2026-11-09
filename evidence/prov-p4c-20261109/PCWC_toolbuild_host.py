#!/usr/bin/env python3
"""PCWC tool-build controller (host side). Runs inside an admitted 3G/4G swap-0 scope; builds unpatched Aeneas b59d5188
(with Charon ML cb50ff16) by re-running the ORIGINAL aspis-r1-r18-tools-20261016 recipe (build-aeneas.sh unchanged, sha256
checked) in the pinned immutable image. The container cgroup is capped at MemoryHigh=3G MemoryMax=4G MemorySwapMax=0 with
the same `sudo -n systemctl set-property --runtime docker-<id>.scope` step the original used; pids limit 64; network none;
read-only root. Time budget 900 s (tool-build class)."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time,re,shutil
E=Path(__file__).resolve().parent
run=sys.argv[1];spec=json.loads((E/(run+'_spec.json')).read_text());assert spec['run']==run
sha=lambda b:hashlib.sha256(b).hexdigest()
out=E/(run+'_out');out.mkdir(exist_ok=False);work=out/'work';work.mkdir()
for k in ['aeneas','charon']:
    a=E/spec['archives'][k]['upload'];assert sha(a.read_bytes())==spec['archives'][k]['sha256'],k
    subprocess.check_call(['tar','xzf',str(a),'-C',str(work),'--no-same-owner'])
sc=E/spec['script']['upload'];assert sha(sc.read_bytes())==spec['script']['sha256'];shutil.copy2(sc,work/'build-aeneas.sh')
(work/'bin').mkdir()
name='pcwc-'+run.lower();img=spec['image']
R=lambda a:subprocess.check_output(a,text=True).strip()
R(['docker','create','--name',name,'--read-only','--network','none','--pids-limit','64','--memory','4g','--memory-swap','4g',
   '--tmpfs','/tmp:rw,mode=1777','-e','HOME=/tmp','-v',str(work)+':/work','--entrypoint','bash',img,'/work/build-aeneas.sh'])
state=json.loads(R(['docker','inspect',name]))[0];assert state['Image']==img and state['State']['Status']=='created'
(out/'container-before.json').write_text(json.dumps(state,indent=2)+'\n')
R(['docker','start',name]);state=json.loads(R(['docker','inspect',name]))[0];pid=state['State']['Pid'];cid=state['Id']
rel=next(x.split(':',2)[2] for x in Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::'))
assert cid in rel,rel;cg=Path('/sys/fs/cgroup')/rel.lstrip('/')
cap={'memory.high':str(3*2**30),'memory.max':str(4*2**30),'memory.swap.max':'0'}
subprocess.check_call(['sudo','-n','systemctl','set-property','--runtime','docker-'+cid+'.scope','MemoryHigh=3G','MemoryMax=4G','MemorySwapMax=0'])
rd=lambda p:p.read_text().strip()
got={k:rd(cg/k) for k in cap};assert got==cap,got
pids=rd(cg/'pids.max')
(out/'preflight.json').write_text(json.dumps(dict(container=cid,image=img,cgroup=str(cg),limits=got,pids_max=pids,events_before=rd(cg/'memory.events')),indent=2)+'\n')
(work/'aeneas-go').write_text('actual container cgroup verified before compiler start\n')
t0=time.monotonic();peak=0;last={};timedout=False
while True:
    st=json.loads(R(['docker','inspect',name]))[0]
    if not st['State']['Running']:break
    if cg.exists():
        try:
            peak=max(peak,int(rd(cg/'memory.current')));last={k:rd(cg/k) for k in ['memory.current','memory.peak','memory.swap.current','memory.events']}
        except FileNotFoundError:pass
    if time.monotonic()-t0>880:
        subprocess.call(['docker','stop','-t','5',name]);timedout=True;break
    time.sleep(.3)
st=json.loads(R(['docker','inspect',name]))[0];rc=st['State']['ExitCode']
(out/'container-after.json').write_text(json.dumps(st,indent=2)+'\n')
(out/'container.log').write_text(subprocess.run(['docker','logs',name],capture_output=True,text=True).stdout)
for f in (work/'aeneas-build-a').glob('*'):shutil.copy2(f,out/('build-a-'+f.name))
r=dict(run=run,exit_status=rc,wall_seconds=round(time.monotonic()-t0,3),sampled_cgroup_peak_bytes=peak,last_cgroup_observation=last,timeout_hit=timedout,limits=got,pids_max=pids)
b=work/'bin/aeneas'
if rc==0 and b.exists():
    r['binary_sha256']=sha(b.read_bytes());r['expected_sha256']=spec['expected_binary_sha256'];r['matches_expected']=r['binary_sha256']==spec['expected_binary_sha256']
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
subprocess.call(['docker','rm',name])
print(json.dumps(r));sys.exit(rc)
