"""Verify retained proof receipts and final source consistency; no prover runs."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
errors=[];receipts=[]
for i in range(1,101):
 p=E/f'XRo_L{i:03}'/'receipt.json';r=json.loads(p.read_text());receipts.append(r)
 for f,h in r['source_hashes'].items():
  if hashlib.sha256((p.parent/'sources'/f).read_bytes()).hexdigest()!=h:errors.append(f'source mismatch {i} {f}')
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(f'caps {i}')
 if int(r['swaps'])!=0:errors.append(f'swap {i}')
 if '-M7000' not in r['command']:errors.append(f'Lean cap {i}')
 if r['exit_status']==0 and any('sorryAx' in x for x in r['print_axioms']):errors.append(f'accepted sorryAx {i}')
latest={r['module']:r for r in receipts}
for p in E.glob('XRo_Join_*.lean'):
 r=latest[p.stem]
 if r['exit_status']!=0:errors.append(f'final failed module {p.name}')
 if hashlib.sha256(p.read_bytes()).hexdigest() not in r['source_hashes'].values():errors.append(f'unchecked final source {p.name}')
 text=p.read_text()
 if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M):errors.append(f'forbidden new proof source {p.name}')
 for theorem in re.findall(r'^.*?\btheorem\s+(\w+)',text,re.M):
  if '#print axioms '+theorem not in text:errors.append(f'axiom query missing {p.name}:{theorem}')
final=receipts[-1]
if final['exit_status']!=0 or len(final['print_axioms'])!=72:errors.append('final 72-name audit')
for line in final['print_axioms']:
 m=re.search(r'axioms: \[([^\]]*)\]',line)
 if m and not set(x.strip() for x in m.group(1).split(',')) <= {'propext','Classical.choice','Quot.sound'}:errors.append('nonstandard final axiom '+line)
root=E.parent.parent/'lean/FJv_Top.lean'
if not root.read_bytes()==(E/'XRo_top_before.lean.txt').read_bytes()==(E/'XRo_top_after.lean.txt').read_bytes():errors.append('root changed')
cleanup=json.loads((E/'XRo_CLEANUP.json').read_text())
if cleanup['live_own_jobs']:errors.append('live own jobs')
pins=json.loads((E/'XRo_COHERENT_PINS.json').read_text())
for name,pin in pins.items():
 seen=next(v for k,v in cleanup['retained_coherent_pins'].items() if k.endswith('/'+name))
 if pin!=seen:errors.append('shared pin changed '+name)
r=subprocess.run(['git','diff','--check'],capture_output=True,text=True)
(E/'XRo_diff_check.log').write_text(r.stdout+r.stderr)
if r.returncode:errors.append('git diff check')
summary=dict(errors=errors,lean_attempts=len(receipts),lean_pass=sum(r['exit_status']==0 for r in receipts),lean_fail=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swap=0,final_new_modules=len(list(E.glob('XRo_Join_*.lean'))),final_axiom_queries=len(final['print_axioms']),fresh_root_audit=False,actual_top_changed=False)
(E/'XRo_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));raise SystemExit(bool(errors))
