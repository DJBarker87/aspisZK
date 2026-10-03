import os,pathlib,json,subprocess,hashlib,glob,re
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r430-constant-proof-attempt-a-20261003');assert not root.exists();root.mkdir()
source=pathlib.Path('/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a/AspisV8R19/R430ReadonlyConstantGraph.lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cgroup():
 rel=next(x.split('::')[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
 p=pathlib.Path('/sys/fs/cgroup')/rel
 return {'path':str(p),**{n:(p/n).read_text().strip() if (p/n).exists() else None for n in ['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events']}}
assert sha(source)=='9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335'
cg=cgroup();assert (cg['memory.high'],cg['memory.max'],cg['memory.swap.max'],cg['pids.max'])==('5368709120','7516192768','0','128')
mem={k:int(v.split()[0])*1024 for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ['MemTotal','MemAvailable']}
cap=7*1024**3;safe=min(40*1024**3,mem['MemTotal']-16*1024**3);assert mem['MemAvailable']-cap>=24*1024**3
useractive=subprocess.check_output(['systemctl','--user','list-units','--all','--plain','--state=running','--no-legend'],text=True)
others=[x for x in useractive.splitlines() if x.split() and x.split()[0].startswith('aspis') and x.split()[0].endswith(('.service','.scope')) and x.split()[0]!='aspis-r430-constant-proof-attempt-a.service'];assert not others,others
systemactive=subprocess.check_output(['systemctl','list-units','--all','--plain','--state=running','--no-legend'],text=True);reservations=[]
for line in systemactive.splitlines():
 if not line.split() or not line.split()[0].startswith('aspis') or not line.split()[0].endswith(('.service','.scope')):continue
 name=line.split()[0];props=dict(x.split('=',1) for x in subprocess.check_output(['systemctl','show',name,'-p','MemoryMax','-p','MemoryCurrent','-p','ExecStart'],text=True).splitlines() if '=' in x);assert props['MemoryMax'].isdigit();reservations.append({'unit':name,**props})
assert cap+sum(int(x['MemoryMax']) for x in reservations)<=safe
heavy=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ['cargo','rustc','charon','charon-driver','aeneas','lean','lean4']];assert not heavy,heavy
os.environ['LEAN_PATH']=':'.join(['/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib',*sorted(glob.glob('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/*/.lake/build/lib/lean')),'/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'])
workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace')
assert (workspace/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.0'
base=['/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean'];version=subprocess.check_output([*base,'--version'],text=True);assert '4.32.0' in version,version
obj=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib')/'AspisV8R19/R430ReadonlyConstantGraph.olean';obj.parent.mkdir(parents=True,exist_ok=True)
command=[*base,'-j1','-M4500','-R','/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','-o',str(obj),str(source)]
(root/'host-before.json').write_text(json.dumps({'cgroup':cg,'mem':mem,'reservations':reservations,'safe_working_limit_bytes':safe,'build_cap_bytes':cap,'heavy_processes':heavy,'other_user_jobs':others,'lean_version':version,'LEAN_PATH':os.environ['LEAN_PATH']},indent=2))
(root/'command.json').write_text(json.dumps(command,indent=2))
with (root/'lean.log').open('wb') as log:run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],stdout=log,stderr=subprocess.STDOUT)
after=cgroup();assert sha(source)=='9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335'
(root/'host-after.json').write_text(json.dumps({'cgroup':after,'source_sha256':sha(source),'olean_sha256':sha(obj) if run.returncode==0 else None},indent=2))
t=(root/'gnu-time.txt').read_text();text=(root/'lean.log').read_text()
def metric(p):
 m=re.search(p,t);return m.group(1).strip() if m else None
r={'target':'AspisV8R19/R430ReadonlyConstantGraph.lean','source_revision':'367345a0407f8869375dcd2f30fda36ca6c4dfcb','source_sha256':'9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335','exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)'),'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0),'swaps':int(metric(r'Swaps:\s*(\d+)') or 0),'complete_print_axioms':re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",text),'lean_version':version,'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'flags':'-j1 -M4500'}}
(root/'receipt.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r));raise SystemExit(run.returncode)
