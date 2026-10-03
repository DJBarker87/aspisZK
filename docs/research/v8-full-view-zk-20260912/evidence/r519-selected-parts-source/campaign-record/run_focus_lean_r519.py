#!/usr/bin/env python3
import pathlib,hashlib,json,subprocess,shlex,re,sys
ROOT=pathlib.Path(__file__).resolve().parents[2]; LOCAL=pathlib.Path(__file__).resolve().parent/'lean-input'
REV=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
HOST='dombarker@100.108.41.90'; OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SRCROOT='/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a'
CACHE='/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib'
WORKSPACE='/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace'
MOD='AspisR519SharedGammaPartsV3'; REMDIR=SRCROOT+'/'+MOD
OUT=pathlib.Path(__file__).resolve().parent/'lean-runs';OUT.mkdir(exist_ok=True)
FILES=['Types.lean','Funs.lean','Axioms.lean']; SHAS={n:hashlib.sha256((LOCAL/n).read_bytes()).hexdigest() for n in FILES}
subprocess.run(['ssh',*OPTS,HOST,shlex.join(['mkdir','-p',REMDIR])],check=True)
for n in FILES:subprocess.run(['scp',*OPTS,str(LOCAL/n),HOST+':'+REMDIR+'/'+n],check=True)

def remote_script(target,unit,run_dir):
 target_path=REMDIR+'/'+target
 obj=CACHE+'/'+MOD+'/'+target[:-5]+'.olean' if target.endswith('.lean') and target!='Axioms.lean' else None
 outpath=obj or ''
 expected=SHAS[target]
 inner=f'''import os,pathlib,subprocess,hashlib,json,re
root=pathlib.Path({run_dir!r});root.mkdir(parents=True,exist_ok=True)
src=pathlib.Path({target_path!r});assert hashlib.sha256(src.read_bytes()).hexdigest()=={expected!r}
unit={unit!r}; cap=7*1024**3
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 n=line.split()[0]
 if n.startswith('aspis'):
  m=subprocess.check_output(['systemctl','--user','show',n,'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  assert m.isdigit(),(n,m);reservations.append((n,int(m)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
cgpath=pathlib.Path('/sys/fs/cgroup')/next(x.split('::')[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
assert (cgpath/'memory.high').read_text().strip()==str(5*1024**3)
assert (cgpath/'memory.max').read_text().strip()==str(7*1024**3)
assert (cgpath/'memory.swap.max').read_text().strip()=='0'
assert (cgpath/'pids.max').read_text().strip()=='128'
mem={{k:int(v.split()[0])*1024 for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ['MemTotal','MemAvailable']}}
assert mem['MemAvailable']-cap>=24*1024**3,mem
cache={CACHE!r};deps=sorted(__import__('glob').glob('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/*/.lake/build/lib/lean'))
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'
os.environ['LEAN_PATH']=':'.join([cache,*deps,aeneas])
workspace=pathlib.Path({WORKSPACE!r});assert (workspace/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.0'
base=['/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean']
version=subprocess.check_output([*base,'--version'],text=True);assert '4.32.0' in version,version
cmd=[*base,'-j1','-M4500','-R',{SRCROOT!r}]
if {outpath!r}:
 pathlib.Path({outpath!r}).parent.mkdir(parents=True,exist_ok=True)
 cmd+=['-o',{outpath!r}]
cmd.append(str(src))
(root/'preflight.json').write_text(json.dumps({{'target':{target!r},'source_sha256':{expected!r},'lean_version':version,'reservations':reservations,'cgroup':{{k:(cgpath/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}},'meminfo_bytes':mem,'LEAN_PATH':os.environ['LEAN_PATH'],'command':cmd,'revision':{REV!r}}},indent=2)+'\\n')
with (root/'lean.log').open('w') as log:result=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=log,stderr=subprocess.STDOUT)
txt=(root/'lean.log').read_text()
def metric(p):
 m=re.search(p,txt);return m.group(1) if m else None
axioms=re.findall(r"'[^\\n]+' (?:depends on axioms: \\[[\\s\\S]*?\\]|does not depend on any axioms)",txt)
receipt={{'target':{target!r},'source_sha256':{expected!r},'source_revision':{REV!r},'exit_status':result.returncode,'wall_time':metric(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (\\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \\(kbytes\\): (\\d+)'),'swaps':metric(r'Swaps: (\\d+)'),'lean_version':version,'lean_path':os.environ['LEAN_PATH'],'command':cmd,'axiom_report_lines':axioms,'olean_sha256':hashlib.sha256(pathlib.Path({outpath!r}).read_bytes()).hexdigest() if {outpath!r} and result.returncode==0 else None}}
(root/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\\n')
print(json.dumps(receipt,indent=2));raise SystemExit(result.returncode)
'''
 return inner

targets=[('Types.lean','types'),('Funs.lean','funs'),('Axioms.lean','axioms')]
for target,label in targets:
 unit='aspis-r519-parts-lean-'+label; remrun='/home/dombarker/project-offloads/aspis-r519-parts-lean-20261003-a/'+label
 run_dir=OUT/label;run_dir.mkdir(parents=True,exist_ok=True)
 remote=remote_script(target,unit,remrun)
 command=['systemd-run','--user','--wait','--collect','--pipe','--unit='+unit,'--working-directory='+SRCROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',remote]
 (run_dir/'launch.json').write_text(json.dumps({'unit':unit,'target':target,'source_sha256':SHAS[target],'source_revision':REV,'command':command},indent=2)+'\n')
 with (run_dir/'ssh.log').open('w') as f:r=subprocess.run(['ssh',*OPTS,HOST,shlex.join(command)],stdout=f,stderr=subprocess.STDOUT)
 (run_dir/'launch-status.json').write_text(json.dumps({'exit_status':r.returncode},indent=2)+'\n')
 for name in ['preflight.json','lean.log','receipt.json']:
  rr=subprocess.run(['scp',*OPTS,HOST+':'+remrun+'/'+name,str(run_dir/name)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  (run_dir/(name+'.copy-status.json')).write_text(json.dumps({'exit_status':rr.returncode,'stderr':rr.stderr.decode(errors='replace')},indent=2)+'\n')
 print(f'=== {target} ===');print((run_dir/'lean.log').read_text() if (run_dir/'lean.log').exists() else (run_dir/'ssh.log').read_text())
 if r.returncode: raise SystemExit(r.returncode)
