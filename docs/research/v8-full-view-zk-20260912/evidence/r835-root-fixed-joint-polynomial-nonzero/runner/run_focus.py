import sys, pathlib, subprocess, shlex, time, json, hashlib, re, uuid
root=pathlib.Path(__file__).resolve().parent.parent
src=pathlib.Path(sys.argv[1]); rel=sys.argv[2] if len(sys.argv)>2 else src.name
host='dombarker@100.108.41.90'; opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a'
cache='/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib'
runid='aspis-focus-'+str(time.time_ns())+'-'+uuid.uuid4().hex[:12]; log=root/'.r21-scratch'/f'{runid}.log'
source_bytes=src.read_bytes(); source_sha=hashlib.sha256(source_bytes).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
snapshot=root/'.r21-scratch'/f'{runid}.source.lean'; snapshot.write_bytes(source_bytes)
receipt_path=root/'.r21-scratch'/f'{runid}.receipt.json'
local_lean=root/'docs/research/v8-full-view-zk-20260912/lean'
dependency_hashes={}
for imp in re.findall(r'^import\s+([A-Za-z0-9_.]+)',source_bytes.decode(),re.M):
 dep=local_lean/(imp.replace('.','/')+'.lean')
 if dep.is_file(): dependency_hashes[imp]=hashlib.sha256(dep.read_bytes()).hexdigest()
receipt={'target':rel,'source_revision':revision,'source_sha256':source_sha,'source_snapshot':str(snapshot),'direct_local_import_sha256':dependency_hashes,'runner_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'log':str(log),'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'measurement_boundary':'GNU time Lean-child RSS; wrapper MemoryPeak is not aggregate Lean RSS.'}
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
subprocess.run(['ssh',*opts,host,'mkdir -p '+shlex.quote(str(pathlib.PurePosixPath(remote,rel).parent))],check=True)
subprocess.run(['scp',*opts,str(src),host+':'+remote+'/'+rel],check=True)
script=f'''import os, glob, subprocess, pathlib, hashlib
assert hashlib.sha256(pathlib.Path({str(pathlib.PurePosixPath(remote,rel))!r}).read_bytes()).hexdigest()=={source_sha!r}
p={cache!r}
deps=sorted(glob.glob('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/*/.lake/build/lib/lean'))
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'
os.environ['LEAN_PATH']=':'.join([p,*deps,aeneas])
obj=p+'/'+{rel!r}[:-5]+'.olean'
os.makedirs(os.path.dirname(obj),exist_ok=True)
workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace')
workspace.mkdir(exist_ok=True)
(workspace/'lakefile.toml').write_text('name = \"aspis_focus\"\\nversion = \"0.0.0\"\\n')
(workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\\n')
cmd=['/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean','-j1','-M4500','-R',{remote!r},'-o',obj,{remote!r}+'/'+{rel!r}]
raise SystemExit(subprocess.call(['/usr/bin/time','-v',*cmd]))
'''
command=['systemd-run','--user','--wait','--collect','--pipe','--unit='+runid,'--working-directory='+remote,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
with log.open('w') as f:
 r=subprocess.run(['ssh',*opts,host,shlex.join(command)],stdout=f,stderr=subprocess.STDOUT)
txt=log.read_text();receipt['exit_status']=r.returncode
for key,pattern in [('wall_time',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),('peak_rss_kib',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)')]:
 match=re.search(pattern,txt)
 if match: receipt[key]=match[1] if key=='wall_time' else int(match[1])
receipt['complete_print_axioms']=re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",txt)
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
print(txt);print('LOG',log,'EXIT',r.returncode,'RECEIPT',receipt_path)
sys.exit(r.returncode)
