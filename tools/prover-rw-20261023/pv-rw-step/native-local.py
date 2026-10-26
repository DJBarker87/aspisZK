"""One focused local check from copied pinned J objects; never builds dependencies."""
from pathlib import Path
import os,sys,subprocess,json,hashlib,re,datetime
r=Path(__file__).resolve().parents[3];a=int(sys.argv[1]);m=sys.argv[2]
assert 23700<=a<=23999 and m.startswith('PV_RW_') and m.replace('_','').isalnum()
e=r/'evidence/pv-rw-step-20261026/local';e.mkdir(exist_ok=True);base=Path('/private/tmp/pv-rw-step-native-local-20261026');cache=base/'shared-cache';backend=base/'backend-cache'
project=r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023';root=r/'docs/research/v8-r0-zk-20261009/lean';source=root/'R1Z'/(m+'.lean')
packages=Path('/Users/dominic/ZK/AspisFormal/.lake/packages');paths=[cache,backend]+[p/'.lake/build/lib/lean' for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (e/f'{a}-input.json').exists()
def imports(s):
 clean=[];depth=0;i=0
 while i<len(s):
  pair=s[i:i+2]
  if pair=='/-':depth+=1;i+=2;continue
  if depth and pair=='-/':depth-=1;i+=2;continue
  if depth:
   if s[i]=='\n':clean.append('\n')
   i+=1;continue
  if pair=='--':
   end=s.find('\n',i);i=len(s) if end<0 else end;continue
  clean.append(s[i]);i+=1
 return [m for line in ''.join(clean).splitlines() if line.startswith('import ') for m in line[7:].split()]
deps={};seen=set()
def visit(name):
 if name in seen:return
 seen.add(name)
 p=next((p/(name.replace('.','/')+'.olean') for p in paths if (p/(name.replace('.','/')+'.olean')).is_file()),None)
 assert p,('missing cached object',name)
 deps[name]=dict(path=str(p),sha256=sha(p))
 src=root/(name.replace('.','/')+'.lean')
 if name.startswith("R1Z.PV_RW_") and src.is_file():
  for child in imports(src.read_text()):visit(child)
for dep in imports(source.read_text()):visit(dep)
cmd=['/usr/bin/time','-l','lake','env','lean','-M7000','--root='+str(root),'-o',str(cache/'R1Z'/(m+'.olean')),str(source)]
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
committed=subprocess.run(['git','show',revision+':'+str(source.relative_to(r))],cwd=r,capture_output=True)
source_committed=committed.returncode==0 and committed.stdout==source.read_bytes()
x=dict(attempt=a,kind='local-cached-J',module='R1Z/'+m,source_sha256=sha(source),source_snapshot=f'{a}.lean.txt',source_revision=revision+('' if source_committed else '+uncommitted'),source_was_uncommitted=not source_committed,runner_sha256=sha(Path(__file__)),deps_fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=cmd,cwd=str(project),dependency_pins=deps,limits=dict(lean_memory_mb=7000),scope='Focused cached local check below 8GiB during host quiet window. No dependency build. Copied J backend/objects and existing matching mathlib81a5d257c8e410db227a6665ed08f64fea08e997; no native Linux libraries. MacOS has no cgroup.',lean_githash='8c9756b28d64dab099da31a4c09229a9e6a2ef35',lean_path=list(map(str,paths)),compiler_sha256=sha(Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')),stdlib_root_sha256=sha(paths[-1]/'Std.olean'),project_pins={str(p):sha(p) for p in [project/'lakefile.toml',project/'lean-toolchain']},backend_root_sha256=sha(backend/'Aeneas.olean'),shared_J_closure_input='23780-input.json',mathlib_source_git=subprocess.check_output(['git','rev-parse','HEAD'],cwd=packages/'mathlib',text=True).strip())
(e/f'{a}.lean.txt').write_bytes(source.read_bytes());(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n')
log=r/f'evidence/pv-rw-step-20261026/local-{a}.log'
with log.open('w') as f:
 ret=subprocess.run(cmd,cwd=project,env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths))),stdout=f,stderr=subprocess.STDOUT).returncode
raw=log.read_text();reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",raw)
x.update(exit_status=ret,wall_seconds=float(re.search(r'([\d.]+) real',raw)[1]),peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size',raw)[1]),swaps=int(re.search(r'(\d+)\s+swaps',raw)[1]),print_axioms=reports,log=f'../local-{a}.log')
(e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
print(raw[:11000]);print(a,ret,x['wall_seconds'],x['peak_rss_bytes'])
assert x['peak_rss_bytes']<8*2**30
if not ret:
 assert reports and 'sorryAx' not in raw and 'error:' not in raw
 for report in reports:
  if 'depends on axioms:' in report:assert set(z.strip() for z in report.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
raise SystemExit(ret)
