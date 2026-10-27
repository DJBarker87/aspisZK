"""Receipt/source consistency audit only; never invokes a compiler or prover."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; latest={}; groups={}; limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for kind,count in [('L',60),('K',20)]:
 rows=[]
 for i in range(1,count+1):
  a=f'LPa_{kind}{i:03}';p=E/a/'receipt.json'
  if not p.exists():errors.append(a+' missing receipt');continue
  r=json.loads(p.read_text());rows.append(r)
  if r['attempt']!=a:errors.append(a+' identity')
  if r['limits']!=limits:errors.append(a+' caps')
  for f,h in r['source_hashes'].items():
   q=p.parent/'sources'/f
   if not q.exists() or sha(q)!=h:errors.append(a+' source '+f)
  if kind=='L' and r['exit_status']==0:
   latest[r['module']]=r
   for line in r['print_axioms']:
    m=re.search(r'\[(.*?)\]',line,re.S)
    if m and not {x.strip() for x in m[1].split(',')}.issubset({'propext','Classical.choice','Quot.sound'}):errors.append(a+' axiom '+line)
 groups[kind]=rows
for module,r in latest.items():
 if not module.startswith('LPa_'):continue
 p=E/(module+'.lean')
 if not p.exists() or sha(p) not in r['source_hashes'].values():errors.append(module+' current source differs')
 if p.exists() and re.search(r'^\s*(?:axiom|sorry|admit)\b|native_decide|set_option\s+(?:maxRecDepth|maxHeartbeats)',p.read_text(),re.M):errors.append(module+' forbidden construct')
for p in E.glob('LPa_*.lean'):
 if p.stem not in latest:errors.append('Unaccepted current Lean file '+p.name)
pins={}
for r in latest.values():
 for v in r['deps_fingerprint']['selected_objects'].values():
  path=v['path']
  if path in pins and pins[path]!=v['sha256']:errors.append('Dependency conflict '+path)
  pins[path]=v['sha256']
script='import sys,json,hashlib;from pathlib import Path; x=json.load(sys.stdin);print(json.dumps({p:(hashlib.sha256(Path(p).read_bytes()).hexdigest() if Path(p).is_file() else None) for p in x}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(list(pins)),text=True,capture_output=True,check=True)
actual=json.loads(r.stdout)
for p,h in pins.items():
 if actual[p]!=h:errors.append('Dependency drift '+p)
(E/'LPa_final-dependency-hashes.json').write_text(json.dumps(actual,indent=2)+'\n')
if sha(Path('lean/ARX_Root.lean'))!=sha(E/'LPa_BEFORE.lean.txt') or sha(E/'LPa_AFTER.lean.txt')!=sha(E/'LPa_BEFORE.lean.txt'):errors.append('Top statement drift')
audit=json.loads((E/'LPa_L060/receipt.json').read_text());plan=json.loads((E/'LPa_audit-plan.json').read_text())
if audit['exit_status']!=0:errors.append('Final audit failed')
if len(audit['print_axioms'])!=len(plan['new_names'])+len(plan['existing_leaves']):errors.append('Audit coverage')
summary=dict(errors=errors,lean_attempts=len(groups['L']),lean_pass=sum(r['exit_status']==0 for r in groups['L']),lean_fail=sum(r['exit_status']!=0 for r in groups['L']),lean_wall_seconds=sum(r['wall_seconds'] for r in groups['L']),lean_peak_rss_kib=max(int(r['peak_rss_kib']) for r in groups['L']),lean_cgroup_peak_bytes=max(int(r['cgroup_memory_peak_bytes']) for r in groups['L']),lean_swaps=sum(int(r['swaps']) for r in groups['L']),kani_runs=len(groups['K']),kani_pass=sum(r['exit_status']==0 for r in groups['K']),kani_fail=sum(r['exit_status']!=0 for r in groups['K']),kani_wall_seconds=sum(r['wall_seconds'] for r in groups['K']),kani_peak_rss_kib=max(int(r['peak_rss_kib']) for r in groups['K']),kani_cgroup_peak_bytes=max(int(r['cgroup_memory_peak_bytes']) for r in groups['K']),kani_swaps=sum(int(r['swaps']) for r in groups['K']),accepted_new_modules=sum(m.startswith('LPa_') for m in latest),unchanged_prerequisite_modules=sum(m.startswith('XRk_') for m in latest),new_theorem_audits=len(plan['new_names']),existing_leaf_audits=len(plan['existing_leaves']),final_dependency_artifacts=len(pins),top_premises_removed=0,elf_gate='BLOCKED: default host build-script linker Resource temporarily unavailable; no fresh pins',duplicate_native_precompile_refusal=1)
(E/'LPa_Verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
raise SystemExit(bool(errors))
