#!/usr/bin/env python3
import pathlib,hashlib,json,subprocess,shlex,sys
H=pathlib.Path(__file__).resolve().parent;W=H.parents[2]
SOURCE=H/'R430ReadonlyConstantGraph.UNVERIFIED.lean';RAW=SOURCE.read_bytes();SHA=hashlib.sha256(RAW).hexdigest()
REV=subprocess.check_output(['git','rev-parse','HEAD'],cwd=W,text=True).strip()
HOST='dombarker@100.108.41.90';OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
RUN=H/sys.argv[1];assert not RUN.exists();RUN.mkdir();(RUN/'source.lean').write_bytes(RAW)
ROOT='/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a';REL='AspisV8R19/R430ReadonlyConstantGraph.lean';TARGET=ROOT+'/'+REL
CACHE='/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib';REMOTE='/home/dombarker/project-offloads/aspis-r430-constant-proof-'+sys.argv[1]+'-20261003'
UNIT='aspis-r430-constant-proof-'+sys.argv[1]
subprocess.run(['ssh',*OPTS,HOST,shlex.join(['mkdir','-p',ROOT+'/AspisV8R19'])],check=True)
subprocess.run(['scp',*OPTS,str(SOURCE),HOST+':'+TARGET],check=True)
remote=r'''import os,pathlib,json,subprocess,hashlib,glob,re
root=pathlib.Path(@REMOTE@);assert not root.exists();root.mkdir()
source=pathlib.Path(@TARGET@)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cgroup():
 rel=next(x.split('::')[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
 p=pathlib.Path('/sys/fs/cgroup')/rel
 return {'path':str(p),**{n:(p/n).read_text().strip() if (p/n).exists() else None for n in ['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events']}}
assert sha(source)==@SHA@
cg=cgroup();assert (cg['memory.high'],cg['memory.max'],cg['memory.swap.max'],cg['pids.max'])==('5368709120','7516192768','0','128')
mem={k:int(v.split()[0])*1024 for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ['MemTotal','MemAvailable']}
cap=7*1024**3;safe=min(40*1024**3,mem['MemTotal']-16*1024**3);assert mem['MemAvailable']-cap>=24*1024**3
useractive=subprocess.check_output(['systemctl','--user','list-units','--all','--plain','--state=running','--no-legend'],text=True)
others=[x for x in useractive.splitlines() if x.split() and x.split()[0].startswith('aspis') and x.split()[0].endswith(('.service','.scope')) and x.split()[0]!=@UNIT_SERVICE@];assert not others,others
systemactive=subprocess.check_output(['systemctl','list-units','--all','--plain','--state=running','--no-legend'],text=True);reservations=[]
for line in systemactive.splitlines():
 if not line.split() or not line.split()[0].startswith('aspis') or not line.split()[0].endswith(('.service','.scope')):continue
 name=line.split()[0];props=dict(x.split('=',1) for x in subprocess.check_output(['systemctl','show',name,'-p','MemoryMax','-p','MemoryCurrent','-p','ExecStart'],text=True).splitlines() if '=' in x);assert props['MemoryMax'].isdigit();reservations.append({'unit':name,**props})
assert cap+sum(int(x['MemoryMax']) for x in reservations)<=safe
heavy=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ['cargo','rustc','charon','charon-driver','aeneas','lean','lean4']];assert not heavy,heavy
os.environ['LEAN_PATH']=':'.join([@CACHE@,*sorted(glob.glob('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/*/.lake/build/lib/lean')),'/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'])
workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace')
assert (workspace/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.0'
base=['/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean'];version=subprocess.check_output([*base,'--version'],text=True);assert '4.32.0' in version,version
obj=pathlib.Path(@CACHE@)/'AspisV8R19/R430ReadonlyConstantGraph.olean';obj.parent.mkdir(parents=True,exist_ok=True)
command=[*base,'-j1','-M4500','-R',@ROOT@,'-o',str(obj),str(source)]
(root/'host-before.json').write_text(json.dumps({'cgroup':cg,'mem':mem,'reservations':reservations,'safe_working_limit_bytes':safe,'build_cap_bytes':cap,'heavy_processes':heavy,'other_user_jobs':others,'lean_version':version,'LEAN_PATH':os.environ['LEAN_PATH']},indent=2))
(root/'command.json').write_text(json.dumps(command,indent=2))
with (root/'lean.log').open('wb') as log:run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],stdout=log,stderr=subprocess.STDOUT)
after=cgroup();assert sha(source)==@SHA@
(root/'host-after.json').write_text(json.dumps({'cgroup':after,'source_sha256':sha(source),'olean_sha256':sha(obj) if run.returncode==0 else None},indent=2))
t=(root/'gnu-time.txt').read_text();text=(root/'lean.log').read_text()
def metric(p):
 m=re.search(p,t);return m.group(1).strip() if m else None
r={'target':@REL@,'source_revision':@REV@,'source_sha256':@SHA@,'exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)'),'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0),'swaps':int(metric(r'Swaps:\s*(\d+)') or 0),'complete_print_axioms':re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",text),'lean_version':version,'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'flags':'-j1 -M4500'}}
(root/'receipt.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r));raise SystemExit(run.returncode)
'''
for k,v in {'@REMOTE@':repr(REMOTE),'@TARGET@':repr(TARGET),'@SHA@':repr(SHA),'@UNIT_SERVICE@':repr(UNIT+'.service'),'@CACHE@':repr(CACHE),'@ROOT@':repr(ROOT),'@REL@':repr(REL),'@REV@':repr(REV)}.items():remote=remote.replace(k,v)
assert '@' not in remote
(RUN/'remote.py').write_text(remote)
argv=['ssh',*OPTS,HOST,shlex.join(['systemd-run','--user','--wait','--collect','--pipe','--unit='+UNIT,'--working-directory='+ROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','-p','KillMode=control-group','-p','TimeoutStopSec=10s','python3','-c',remote])]
(RUN/'launch.json').write_text(json.dumps({'argv':argv,'source_sha256':SHA,'source_revision':REV},indent=2))
with (RUN/'ssh.log').open('wb') as log:job=subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT)
(RUN/'launch-status.json').write_text(json.dumps({'ssh_exit_status':job.returncode},indent=2))
for file in ['command.json','host-before.json','host-after.json','lean.log','gnu-time.txt','receipt.json']:
 cp=subprocess.run(['scp',*OPTS,HOST+':'+REMOTE+'/'+file,str(RUN/file)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (RUN/(file+'.copy-status.json')).write_text(json.dumps({'exit_status':cp.returncode,'stderr':cp.stderr.decode(errors='replace')},indent=2))
print((RUN/'lean.log').read_text() if (RUN/'lean.log').exists() else (RUN/'ssh.log').read_text());print('TERMINAL',job.returncode);sys.exit(job.returncode)
