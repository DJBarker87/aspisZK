"""One bounded diagnostic translation; requires reviewed source and successful build."""
import pathlib,json,hashlib,subprocess,shlex,sys
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
ROOT='/home/dombarker/project-offloads/aspis-r614-scalar-constants-candidate-20261004-a'
OUT='/home/dombarker/project-offloads/aspis-r614-combine-beta-translation-20261004-c'
INP='/home/dombarker/project-offloads/aspis-r604-combine-beta-generic-20261004-b/R604CombineBetaGeneric.llbc'
SHA='5391af65767eee12ff76fbddbe2be730f4cad8af24d526f6030140539fc4ec44'
# Root creates approval.json only after inspecting exact source diff and successful build.
a=json.loads((HERE/'approval.json').read_text());assert a['source_diff_reviewed'] and a['build_exit_status']==0
remote=r'''import pathlib,json,hashlib,subprocess,re,sys
binary=pathlib.Path(@BIN@);inp=pathlib.Path(@INP@);out=pathlib.Path(@OUT@)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert h(binary)==@BSHA@ and h(inp)==@ISHA@
assert not out.exists(),out
for p,sha in @PINS@.items():assert h(pathlib.Path(p))==sha,(p,sha)
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
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR614SelectedCombineBeta','-dest',str(out/'generated'),'-subdir','AspisR614SelectedCombineBeta','-split-files','-emit-json',str(inp)]
(out/'command.json').write_text(json.dumps({'command':cmd,'literal_candidate_binary_sha':@BSHA@,'immutable_input_sha':@ISHA@,'caps':limits,'reservations':reservations,'timeout_seconds':180,'source_pins':@PINS@,'formal_status':'private diagnostic translation only'},indent=2)+'\n')
with (out/'translation.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','timeout','--signal=TERM','--kill-after=5s','180s',*cmd],stdout=f,stderr=subprocess.STDOUT)
t=(out/'translation.log').read_text(errors='replace')
def metric(rx):
 m=re.search(rx,t);return m.group(1) if m else None
files={str(p.relative_to(out)):h(p) for p in sorted((out/'generated').rglob('*')) if p.is_file()}
d={'exit_status':r.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \(kbytes\): (\d+)'),'swaps':metric(r'Swaps: (\d+)'),'input_sha':h(inp),'binary_sha':h(binary),'generated_files':files,'lean_compiled':False,'axioms':'N/A translation not a formal proof'}
(out/'result.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));sys.exit(r.returncode)
'''
for k,v in {'BIN':a['binary_path'],'BSHA':a['binary_sha256'],'INP':INP,'ISHA':SHA,'OUT':OUT,'PINS':a['source_pins']}.items():remote=remote.replace('@'+k+'@',repr(v))
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r614-combine-beta-translation-20261004-c','--working-directory='+ROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=200s','python3','-c',remote]
(HERE/'translation-launch.json').write_text(json.dumps({'systemd_argv':cmd,'approval':a},indent=2)+'\n')
with (HERE/'translation-ssh.log').open('w') as f:r=subprocess.run(['ssh',*OPTS,HOST,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
for n in ['command.json','translation.log','result.json']:subprocess.run(['scp',*OPTS,f'{HOST}:{OUT}/{n}',str(HERE/n)],check=False)
(HERE/'translation-launch-exit.json').write_text(json.dumps({'exit_status':r.returncode})+'\n')
if (HERE/'result.json').exists():
 d=json.loads((HERE/'result.json').read_text());print(json.dumps(d))
 if d['generated_files']:
  subprocess.run(['ssh',*OPTS,HOST,shlex.join(['tar','-C',OUT,'-czf',OUT+'/generated.tgz','generated'])],check=True)
  subprocess.run(['scp',*OPTS,f'{HOST}:{OUT}/generated.tgz',str(HERE/'generated.tgz')],check=True)
sys.exit(r.returncode)
