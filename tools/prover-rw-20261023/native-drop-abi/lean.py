"""Run one assigned env-J attempt; retain exact inputs and all diagnostics."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
E=H/'native-drop-abi/lean'; E.mkdir(parents=True,exist_ok=True)
a=int(sys.argv[1]); module=sys.argv[2]; assert 11570<=a<=11599
assert len(list(E.glob('*-input.json'))) < 30, 'new Lean attempt ceiling exhausted'
assert module.startswith('R1Z/ProverRwNativeDropABI')
assert not (E/f'{a}-input.json').exists(), 'attempt receipt already exists'
source=J/'sources'/(module+'.lean'); s=source.read_text(); deps=[]
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[J/'objects',*[Path(x) for x in env['LEAN_PATH'].split(':')]]
seen=set()
def imports(text):
 # Discard nested Lean block comments and line comments before reading imports.
 clean=[];depth=0;i=0
 while i<len(text):
  pair=text[i:i+2]
  if pair=='/-':depth+=1;i+=2;continue
  if depth and pair=='-/':depth-=1;i+=2;continue
  if depth:
   if text[i]=='\n':clean.append('\n')
   i+=1;continue
  if pair=='--':
   end=text.find('\n',i);i=len(text) if end<0 else end;continue
  clean.append(text[i]);i+=1
 return [m for l in ''.join(clean).splitlines() if l.startswith('import ') for m in l[7:].split()]
def visit(m):
 if m in seen:return
 seen.add(m)
 rel=m.replace('.','/')
 obj=next((b/(rel+'.olean') for b in roots if (b/(rel+'.olean')).is_file()),None)
 assert obj,('missing dependency object',m)
 src=J/'sources'/(rel+'.lean')
 children=imports(src.read_text()) if src.is_file() else []
 deps.append(dict(module=m,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),resolved_object=str(obj),source_imports=children))
 for child in children:visit(child)
for m in imports(s):visit(m)
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
(E/f'{a}.lean.txt').write_text(s)
(E/f'{a}-input.json').write_text(json.dumps(dict(module=module,source_revision=(E/'revision.txt').read_text().strip(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),dependencies=deps,deps_fingerprint=fp,source_path=str(source)),indent=2)+'\n')
p=subprocess.run(['sh',str(H/'src/tools/prover-rw-20261023/native-drop/run-joint.sh'),str(a),module,'J','7000','7',fp],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr)
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
 q=T/f'{kind}-{a}.{ext}'
 if q.exists():(E/q.name).write_bytes(q.read_bytes())
log=(E/f'out-{a}.log').read_text() if (E/f'out-{a}.log').exists() else ''
t=(E/f'time-{a}.log').read_text() if (E/f'time-{a}.log').exists() else ''
rec=json.loads((E/f'{a}-input.json').read_text());rec.update(attempt=a,launcher_exit=p.returncode,exit_status=int(re.search(r'^exit=(\d+)',log,re.M)[1]) if re.search(r'^exit=(\d+)',log,re.M) else None,time_log=t,print_axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log),errors=[l for l in log.splitlines() if 'error:' in l],limits=dict(lean_memory_mb=7000,memory_high='5G',memory_max='7G',swap_max=0,tasks_max=64))
(E/f'{a}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
sys.exit(0 if rec['exit_status']==0 else 1)
