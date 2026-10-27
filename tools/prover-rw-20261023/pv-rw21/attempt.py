"""One module through the restored shared launcher, retaining exact receipts.
No launcher, environment, cap, locking or monitoring infrastructure is changed.
"""
from pathlib import Path
import subprocess,json,sys,shlex,hashlib,datetime,re,base64,zlib
r=Path(__file__).resolve().parents[3];a=int(sys.argv[1]);module=sys.argv[2]
assert 37700<=a<=37999
flag=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
assert flag.exists()
e=r/'evidence/pv-rw21-20261027';e.mkdir(exist_ok=True)
assert not (e/f'{a}-input.json').exists()
h='dombarker@100.108.41.90';b='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';j='/home/dombarker/project-offloads/aspis-joint-20261019';d=b+'/pv-rw21';t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
def ssh(cmd,**kw):return subprocess.run(['ssh',h,cmd],text=True,capture_output=True,**kw)
def py(code):return ssh('python3 -c '+shlex.quote(code))
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

src=Path(sys.argv[3]) if len(sys.argv)>3 else r/'docs/research/v8-r0-zk-20261009/lean'/(module.replace('.','/')+'.lean')
src=src.resolve()
s=src.read_text();revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
committed=subprocess.run(['git','show',revision+':'+str(src.relative_to(r))],cwd=r,capture_output=True)
source_uncommitted=committed.returncode!=0 or committed.stdout!=src.read_bytes()
revision+=('+uncommitted' if source_uncommitted else '')
x={'attempt':a,'module':module,'source_revision':revision,'source_path':str(src),'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'gate_flag_contents':flag.read_text(),'limits':{'lean_memory_mb':7000,'memory_high':'6G','memory_max':'8G','swap_max':0,'tasks_max':128},'launcher':'/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh'}
q=ssh('mkdir -p '+d+'; python3 '+b+'/src/tools/prover-rw-20261023/native-entropy/reservation.py '+d+f'/{a}-admission.json > '+d+f'/{a}-admission.log 2>&1; pv_rw_status=$?; cat '+d+f'/{a}-admission.log; exit $pv_rw_status')
(e/f'{a}-admission.log').write_text(q.stdout+q.stderr)
ad=ssh('cat '+d+f'/{a}-admission.json');(e/f'{a}-admission.json').write_text(ad.stdout)
if q.returncode:
 x.update(charged=False,preflight_exit=q.returncode,reason=q.stdout+q.stderr);(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n');print(x['reason']);sys.exit(78)
# Inspect and pin direct imported objects before changing the shared source.
graph={}
focused=e/'focused-dependencies.json'
if focused.exists():
 for row in json.loads(focused.read_text())['order']:
  if row.get('imports') is not None:graph[row['module']]=row['imports']
  if row.get('source') and (r/row['source']).is_file():graph[row['module']]=imports((r/row['source']).read_text())
for p in (r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('ProverRw*.lean'):
 graph['R1Z.'+p.stem]=imports(p.read_text())
x['dependency_fingerprint_schema']='transitive-known-source-imports-v1'
code="""import json,hashlib
from pathlib import Path
j=Path(J);env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[j/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')];rows=[];seen=set();graph=GRAPH

def visit(name):
 if name in seen:return
 seen.add(name)
 for child in graph.get(name,[]):visit(child)
 rel=name.replace('.','/')+'.olean';p=next((x/rel for x in roots if (x/rel).is_file()),None)
 rows.append({'module':name,'object':str(p) if p else None,'sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p else None})
for name in NAMES:visit(name)
print(json.dumps(rows))
""".replace('J',repr(j),1).replace('GRAPH',"json.loads(__import__('zlib').decompress(__import__('base64').b64decode("+repr(base64.b64encode(zlib.compress(json.dumps(graph).encode())).decode())+")))",1).replace('NAMES',repr(imports(s)),1)

q=py(code);assert q.returncode==0,q.stderr
x['dependencies']=json.loads(q.stdout);x['deps_fingerprint']=hashlib.sha256(json.dumps(x['dependencies'],sort_keys=True).encode()).hexdigest()
missing=[v['module'] for v in x['dependencies'] if not v['object']]
if missing:
 x.update(charged=False,missing_dependencies=missing);(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n');print('missing dependencies',missing);sys.exit(66)
rel=module.replace('.','/');dest=j+'/sources/'+rel+'.lean'
# Snapshot any overwritten shared source/object in this branch-owned directory.
code=f"from pathlib import Path; import shutil; p=Path({dest!r}); o=Path({(j+'/objects/'+rel+'.olean')!r}); b=Path({(d+'/codex-cx-prover-rw-20261023/'+str(a))!r}); b.mkdir(parents=True,exist_ok=True); [(shutil.copy2(f,b/f.name)) for f in [p,o] if f.exists()]; p.parent.mkdir(parents=True,exist_ok=True)"
q=py(code);assert q.returncode==0,q.stderr
subprocess.run(['scp',str(src),h+':'+dest],check=True,capture_output=True)
(e/f'{a}.lean.txt').write_text(s);x['target']=[x['launcher'],str(a),rel,'J','7000','8',x['deps_fingerprint']]
(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n')
q=ssh('sh '+' '.join(shlex.quote(v) for v in x['target']));launcher_exit=q.returncode;(e/f'{a}-wrapper.log').write_text(q.stdout+q.stderr)
for name,remote in [('out',f'out-{a}.log'),('time',f'time-{a}.log'),('sha',f'sha-{a}.txt')]:
 v=ssh('cat '+t+'/'+remote);(e/f'{a}-{name}.log').write_text(v.stdout)
raw=(e/f'{a}-out.log').read_text();tm=(e/f'{a}-time.log').read_text()
metric=lambda key:re.search(re.escape(key)+r':\s*(.*)',tm)
exitm=re.search(r'^exit=(\d+)',raw,re.M)
x.update(charged=bool(tm),launcher_exit=launcher_exit,exit_status=int(exitm[1]) if exitm else None,wall_time=metric('Elapsed (wall clock) time (h:mm:ss or m:ss)')[1] if metric('Elapsed (wall clock) time (h:mm:ss or m:ss)') else None,peak_rss_kib=int(metric('Maximum resident set size (kbytes)')[1]) if metric('Maximum resident set size (kbytes)') else None,swaps=int(metric('Swaps')[1]) if metric('Swaps') else None,print_axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",raw),errors=raw)
(e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');print(raw[-9000:]);print({k:x[k] for k in ['attempt','charged','exit_status','wall_time','peak_rss_kib','swaps']})
sys.exit(x['exit_status'] if x['exit_status'] is not None else launcher_exit or 78)
