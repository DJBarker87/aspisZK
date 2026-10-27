from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; lean=[]; kani=[]; latest={}
for i in range(1,101):
 a=f'XRl_L{i:03}';p=E/a/'receipt.json'
 if i==81:
  assert not p.exists();assert json.loads((E/(a+'-refusal.json')).read_text())['charged_to_budget'];continue
 r=json.loads(p.read_text());lean.append(r)
 if r['attempt']!=a:errors.append(a+' identity')
 for n,h in r['source_hashes'].items():
  q=E/a/'sources'/n
  if not q.exists() or sha(q)!=h:errors.append(a+' source '+n)
 if r['exit_status']==0:
  latest[r['module']]=r
  for l in r['print_axioms']:
   if 'sorryAx' in l:errors.append(a+' diagnostic axiom accepted')
   m=re.search(r'\[(.*?)\]',l,re.S)
   if m and not set(x.strip() for x in m[1].split(',')).issubset({'propext','Classical.choice','Quot.sound'}):errors.append(a+' axioms '+l)
 for key,value in [('memory.high','6442450944'),('memory.max','8589934592'),('memory.swap.max','0'),('pids.max','64')]:
  if r['limits'][key]!=value:errors.append(a+' cap '+key)
for i in range(1,11):
 a=f'XRl_K{i:03}';r=json.loads((E/a/'receipt.json').read_text());kani.append(r)
 for n,h in r['source_hashes'].items():
  q=E/a/'sources'/n
  if not q.exists() or sha(q)!=h:errors.append(a+' source '+n)
for p in E.glob('XRl_*.lean'):
 if p.stem not in latest:errors.append('No green current module '+p.name);continue
 r=latest[p.stem]
 if sha(p) not in r['source_hashes'].values():errors.append('Current source differs '+p.name)
 if re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()):errors.append('Forbidden proof construct '+p.name)
# Re-pin actual direct dependency artifacts of the final selected green cohort.
pins={}
for r in latest.values():
 for k,v in r['deps_fingerprint']['selected_objects'].items():
  path=v['path']
  if path in pins and pins[path]!=v['sha256']:errors.append('Final direct dependency conflict '+path)
  pins[path]=v['sha256']
script='import sys,json,hashlib; from pathlib import Path; ps=json.load(sys.stdin); print(json.dumps({p:(hashlib.sha256(Path(p).read_bytes()).hexdigest() if Path(p).is_file() else None) for p in ps}))'
host=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(script)],input=json.dumps(list(pins)),text=True,capture_output=True,check=True)
actual=json.loads(host.stdout)
for p,h in pins.items():
 if actual[p]!=h:errors.append('Final dependency hash drift '+p)
(E/'XRl_final_dependency_hashes.json').write_text(json.dumps(actual,indent=2)+'\n')
base=Path('lean/ARX_Root.lean')
if sha(base)!=sha(E/'XRl_ARX_Root.BEFORE.lean.txt') or sha(base)!=sha(E/'XRl_ARX_Root.AFTER.lean.txt'):errors.append('Actual top statement drift')
summary=dict(errors=errors,lean_allocations=100,lean_compiler_invocations=len(lean),lean_pass=sum(r['exit_status']==0 for r in lean),lean_fail=sum(r['exit_status']!=0 for r in lean),precompiler_refusals=1,lean_wall_seconds=sum(r['wall_seconds'] for r in lean),lean_peak_rss_kib=max(int(r['peak_rss_kib']) for r in lean),lean_swaps=sum(int(r['swaps']) for r in lean),kani_runs=len(kani),kani_pass=sum(r['exit_status']==0 for r in kani),kani_fail=sum(r['exit_status']!=0 for r in kani),kani_wall_seconds=sum(r['wall_seconds'] for r in kani),kani_peak_rss_kib=max(int(r['peak_rss_kib']) for r in kani),kani_swaps=sum(int(r['swaps']) for r in kani),selected_green_modules=len(latest),final_dependency_artifacts=len(pins),actual_top_sha256=sha(base),top_premises_removed=0)
(E/'XRl_Verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
raise SystemExit(bool(errors))
