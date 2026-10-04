#!/usr/bin/env python3
"""One authorized unchanged-binary translation of the exact R664 Option LLBC."""
import hashlib,json,pathlib,shlex,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
ROOT='/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a'
BIN='/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-build-output-20261004-b/aeneas-r614-m31-result-constructor-candidate-20261004-b'
BSHA='0632dabd94aa511685d721738c5685921fd1110663fc1295318053d5c1f8530a'
INP='/home/dombarker/project-offloads/aspis-r664-owned-fold-option-wrappers-capture-20261004-a/R664OwnedPrimalFoldOptionWrappers.llbc'
ISHA='090797a384c3ecefcc28b03ec4b61f0796804bf68326a7044c61aa2e9b217a2a'
OUT='/home/dombarker/project-offloads/aspis-r664-option-wrapper-aeneas-20261004-a'
PINS={
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/extract/ExtractBase.ml':'9706e37373540d079da15ff7ce06ce1186210ea43e96fe41bd579fc17b1c8385',
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/extract/Extract.ml':'9a5bba343ebfc6a030cad9611eb0afa88266851c78f2704e5cead33fe8eec251',
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/extract/ExtractTypes.ml':'cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25',
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/Translate.ml':'19f7e1b91e2a066e24c4231322ae3d5a78464c9ad0f56e8d2cb6358a65837ea5',
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/symbolic/SymbolicToPureTypes.ml':'0e4a4f44c6fcad311e4d67f831d7c5c0efd862b01bb315d1b28f3d0867a47e02',
 '/home/dombarker/project-offloads/aspis-r614-m31-result-constructor-candidate-20261004-a/src/symbolic/SymbolicToPureExpressions.ml':'fbb961950190f41296090ce5281704f521cbb6d36a4d56a1e27df8db2884009b',
}
remote=r'''import pathlib,json,hashlib,subprocess,re,sys
binary=pathlib.Path(__BIN__);inp=pathlib.Path(__INP__);out=pathlib.Path(__OUT__)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert binary.is_file() and h(binary)==__BSHA__,(binary,h(binary))
assert inp.is_file() and h(inp)==__ISHA__,(inp,h(inp))
assert not out.exists(),out
for p,sha in __PINS__.items():assert h(pathlib.Path(p))==sha,(p,sha)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'},limits
reservations=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True).splitlines():
 q=line.split()
 if q and q[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',q[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((q[0],int(v)))
assert sum(v for _,v in reservations)<=40*2**30,reservations
out.mkdir(mode=0o700)
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR664OwnedFoldOptionWrappers','-dest',str(out/'generated'),'-subdir','AspisR664OwnedFoldOptionWrappers','-split-files','-emit-json',str(inp)]
(out/'command.json').write_text(json.dumps({'command':cmd,'binary_sha256':__BSHA__,'input_sha256':__ISHA__,'caps':limits,'reservations':reservations,'timeout_seconds':180,'source_pins':__PINS__,'formal_status':'diagnostic translation only; not a proof'},indent=2)+'\n')
with (out/'translation.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','timeout','--signal=TERM','--kill-after=5s','180s',*cmd],stdout=f,stderr=subprocess.STDOUT)
t=(out/'translation.log').read_text(errors='replace')
def metric(rx):
 m=re.search(rx,t);return m.group(1) if m else None
files={str(p.relative_to(out)):h(p) for p in sorted((out/'generated').rglob('*')) if p.is_file()}
d={'exit_status':r.returncode,'wall_time':metric(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (\\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \\(kbytes\\): (\\d+)'),'swaps':metric(r'Swaps: (\\d+)'),'input_sha':h(inp),'binary_sha':h(binary),'generated_files':files,'lean_compiled':False,'axioms':'N/A; translation is not a formal proof'}
(out/'result.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));sys.exit(r.returncode)
'''
for k,v in {'__BIN__':BIN,'__BSHA__':BSHA,'__INP__':INP,'__ISHA__':ISHA,'__OUT__':OUT,'__PINS__':PINS}.items():remote=remote.replace(k,repr(v))
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r664-option-wrapper-aeneas-20261004-a','--working-directory='+ROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=200s','python3','-c',remote]
(HERE/'translation-launch.json').write_text(json.dumps({'systemd_argv':cmd,'binary':BIN,'binary_sha256':BSHA,'input':INP,'input_sha256':ISHA,'fresh_output_root':OUT,'source_pins':PINS,'preflight_memavailable_bytes':56022675456,'preflight_running_aspis_units':[],'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128,'RuntimeMaxSec':'200s'},'authorized_scope':'one unchanged-binary translation of exact new Option LLBC'},indent=2)+'\n')
with (HERE/'translation-ssh.log').open('w') as f:r=subprocess.run(['ssh',*OPTS,HOST,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
(HERE/'translation-launch-exit.json').write_text(json.dumps({'ssh_exit_status':r.returncode})+'\n')
for n in ['command.json','translation.log','result.json']:
 subprocess.run(['scp',*OPTS,f'{HOST}:{OUT}/{n}',str(HERE/'aeneas-'+n)],check=False)
if (HERE/'aeneas-result.json').exists():
 d=json.loads((HERE/'aeneas-result.json').read_text());print(json.dumps(d,indent=2))
 if d.get('generated_files'):
  subprocess.run(['ssh',*OPTS,HOST,shlex.join(['tar','-C',OUT,'-czf',OUT+'/generated.tgz','generated'])],check=True)
  subprocess.run(['scp',*OPTS,f'{HOST}:{OUT}/generated.tgz',str(HERE/'generated.tgz')],check=True)
sys.exit(r.returncode)
