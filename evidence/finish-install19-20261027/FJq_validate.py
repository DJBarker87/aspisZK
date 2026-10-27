"""Read-only validation of retained source, receipts and ledger; no prover run."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];accepted={};violations=[]
for n in range(1,101):
 name=f'FJq_{n:03}';cfg=P/(name+'.json');assert cfg.exists(),name
 f=P/name/'receipt.json'
 if f.exists():
  x=json.loads(f.read_text());x['compiler_started']=True
  assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},name
  assert '-M7000' in x['command'] and '-j1' in x['command'],name
  if x['exit_status']==0:
   for source,h in x['source_hashes'].items():accepted.setdefault((source,h),[]).append(name)
   for line in x['print_axioms']:
    m=re.search(r'depends on axioms: \[([^]]*)\]',line)
    if m and not set(m[1].split(', '))<={'propext','Classical.choice','Quot.sound'}:violations.append((name,line))
 else:
  x=json.loads((P/(name+'-preflight.json')).read_text());assert not x['compiler_started']
 rows.append(x)
(P/'FJq_attempts.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in rows))
modules=[];forbidden=[]
for f in sorted((R/'lean').glob('FJq_*.lean')):
 h=digest(f);passed=accepted.get((f.name,h),[])
 modules.append(dict(source=str(f.relative_to(R)),sha256=h,passing_receipts=passed))
 for match in re.finditer(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s|\bset_option\s+(?:maxRecDepth|maxHeartbeats)\b',f.read_text(),re.M):forbidden.append((f.name,match[0]))
assert not forbidden,forbidden
assert not violations,violations
assert all(x['passing_receipts'] for x in modules),[x for x in modules if not x['passing_receipts']]
last=json.loads((P/'FJq_100/receipt.json').read_text());assert last['exit_status']==0
expected=set(json.loads((P/'FJq_audit-targets.json').read_text())['roots'])
printed={m[1] for line in last['print_axioms'] if (m:=re.match("'([^']+)'",line))}
assert expected<=printed,expected-printed
baseline='aa9a14c895fdbf2c4144d986cab82c750267a7e3'
tracked=subprocess.check_output(['git','diff','--name-only',baseline],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
outside=[f for f in tracked+untracked if not(f.startswith('lean/FJq_') or f.startswith('evidence/finish-install19-20261027/'))]
assert not outside,outside
pins=json.loads((P/'FJq_baseline-pins.json').read_text())
roots=[]
for f,h in pins['files'].items():
 current=digest(R/f);old=hashlib.sha256(subprocess.check_output(['git','show',baseline+':'+f],cwd=R)).hexdigest()
 roots.append(dict(path=f,before_sha256=old,after_sha256=current,unchanged=current==h==old))
assert all(x['unchanged'] for x in roots)
lean=[x for x in rows if x['compiler_started']]
result=dict(charged_lean_attempts=len(rows),compiler_starts=len(lean),passes=sum(x['exit_status']==0 for x in lean),compiler_errors=sum(x['exit_status']!=0 for x in lean),preflight_errors=100-len(lean),kani_runs=0,budget_exhausted=True,current_modules=modules,unverified_current=[],forbidden_source=forbidden,accepted_nonstandard_axioms=violations,audit_unique_roots=len(printed),new_theorem_roots=len(expected),adopted_root_pins=roots,outside_owned_edits=outside,maximum_peak_rss_kib=max(int(x['peak_rss_kib']) for x in lean),swaps=sorted({x['swaps'] for x in lean}),final_target=last['sources'],final_exit=last['exit_status'],final_wall_seconds=last['wall_seconds'],final_peak_rss_kib=last['peak_rss_kib'],final_revision=last['source_revision'],final_source_hashes=last['source_hashes'],frozen_artifacts='Inherited, not reproduced; no shipped-source change',ledger=json.loads((P/'FJq_recount.json').read_text()))
(P/'FJq_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['charged_lean_attempts','compiler_starts','passes','compiler_errors','preflight_errors','kani_runs','audit_unique_roots','new_theorem_roots','maximum_peak_rss_kib','swaps','unverified_current','outside_owned_edits']},indent=2))
