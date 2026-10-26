"""Offline receipt, source, axioms and unchanged-top ledger checks; no prover."""
from pathlib import Path
import hashlib,json,re,sys
from collections import Counter
E=Path(__file__).resolve().parent; R=E.parents[1]; final='--final' in sys.argv
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
canonical={p.name:p for p in (R/'docs/research/100bit-spend-path-20261013/lean').glob('*.lean')}
canonical.update({p.name:p for p in (R/'lean').glob('*.lean')})
rows=[]
for p in sorted(E.glob('ARR_*/receipt.json')):
 d=json.loads(p.read_text())
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in d['command'] and d['swaps']=='0'
 assert d['source_revision'] and d['deps_fingerprint']['selected_objects']
 for name,h in d['source_hashes'].items():
  assert sha(p.parent/'sources'/name)==h,(d['attempt'],name,'snapshot')
  if d['exit_status']==0:assert sha(canonical[name])==h,(d['attempt'],name,'delivered')
 if d['exit_status']==0:
  for line in d['print_axioms']:
   for m in re.finditer(r'axioms:\s*\[([^\]]*)\]',line,re.S):
    assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},line
 rows.append(d)
assert len(rows)<=100 and len({d['attempt'] for d in rows})==len(rows)
(E/'ARR_attempts.jsonl').write_text(''.join(json.dumps(d)+'\n' for d in rows))
accepted={name for d in rows if d['exit_status']==0 for name in d['source_hashes'] if name.startswith('ARR_')}
own={p.name:p for p in (R/'lean').glob('ARR_*.lean')}
for p in own.values():
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
if final:
 assert len(rows)==100
 assert accepted==set(own),(accepted,set(own))
 audits=(E/'ARR_101/stdout.log').read_text()
 for p in own.values():
  if p.stem=='ARR_FinalAudit':continue
  for theorem in re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M):
   assert f"'AspisR1.{p.stem}.{theorem}'" in audits,(p.name,theorem)
 assert 'sorryAx' not in audits
before=E/'ARR_BEFORE_SOURCE.lean.txt';after=E/'ARR_AFTER_SOURCE.lean.txt'
assert before.read_bytes()==after.read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
baseline=R/'evidence/recount10-20261026/Rc10_premises.json';old=json.loads(baseline.read_text())
count={}
for scope in ['actual antecedent','deployment only','deployment alias']:
 counter=Counter(r['classification'] for r in old['rows'] if r['scope']==scope)
 count[scope]={'rows':sum(counter.values()),'classes':{k:counter[k] for k in 'TPGC'}}
 assert count[scope]['classes']==old['counts'][scope]['classes']
counter=Counter(r['classification'] for r in old['rows'] if r['scope']!='deployment alias')
count['deduplicated actual plus non-alias deployment']={'rows':sum(counter.values()),'classes':{k:counter[k] for k in 'TPGC'}}
assert count['deduplicated actual plus non-alias deployment']['classes']=={'T':89,'P':16,'G':13,'C':0}
ledger=dict(actual_theorem='AspisR1.Rc10_Top.deployed',method=old['method'],baseline_path=str(baseline.relative_to(R)),baseline_sha256=sha(baseline),rows=old['rows'],aliases=old['aliases'],before=count,after=count,removed=[],added=[],reclassified=[],delta={k:0 for k in 'TPGC'},source_before_sha256=sha(before),source_after_sha256=sha(after),scope='Literal Rc10 root unchanged. ARR interface diagnostics and conditional factory obstruction get no deployed premise-removal credit. L159/L185 and L181 retained.')
(E/'ARR_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
for p in E.rglob('*'):
 assert p.suffix not in ['.olean','.elf','.tar','.gz','.ir'],p
summary=dict(lean_attempts=len(rows),kani_runs=0,passes=sum(d['exit_status']==0 for d in rows),failures=[d['attempt'] for d in rows if d['exit_status']],dependency_builds=sum(not d['sources'][0].startswith('ARR_') for d in rows),total_wall_seconds=sum(d['wall_seconds'] for d in rows),max_peak_rss_kib=max(int(d['peak_rss_kib']) for d in rows),swaps=0,prelaunch_only=['ARR_002'],final=final,root_unchanged=True,ledger_delta=ledger['delta'],no_full_release_replay=True,axioms='Standard only on passing targets; failed outputs excluded',admission_retries={p.name:json.loads(p.read_text()) for p in E.glob('ARR_*-retries.json') if json.loads(p.read_text())})
(E/'ARR_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
