"""Static evidence validation only; never invokes Lean/Rust/Kani."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=sorted(P.glob('BEk_*/receipt.json'))
assert len(receipts)==100,len(receipts)
rows=[];passed=0;printed=[];audited=set()
for p in receipts:
 r=json.loads(p.read_text());n=int(r['attempt'].split('_')[1]);assert 1<=n<=100
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command'] and r['command'][1:3]==['env','lean']
 assert r['source_revision'] and r['deps_fingerprint']['selected_objects']
 assert int(r['swaps'])==0
 assert r['exit_status'] not in [124,137],r['attempt']
 for name,h in r['source_hashes'].items():assert sha(p.parent/'sources'/name)==h
 assert (P/(r['attempt']+'-reservation.json')).exists()
 reservation=json.loads((P/(r['attempt']+'-reservation.json')).read_text());assert reservation['allowed']
 assert (P/(r['attempt']+'-barrier.log')).exists()
 if r['exit_status']==0:
  passed+=1
  for line in r['print_axioms']:
   # Universe suffixes are shown by pp.all at the actual root.
   line=re.sub(r'\.\{[^}]*\}','',line)
   assert 'sorryAx' not in line
   m=re.search(r'axioms: \[(.*)\]',line)
   if m:assert set(m[1].split(', ')) <= {'propext','Classical.choice','Quot.sound',''}
   printed.append(line)
   if "'" in line:audited.add(line.split("'")[1])
 rows.append({k:r[k] for k in ['attempt','sources','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','print_axioms']})
new=[]
for file in sorted((R/'lean').glob('BEk_*.lean')):
 s=file.read_text()
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)', '\n'.join(x for x in s.splitlines() if not x.startswith('#print axioms'))),file
 ns=re.search(r'^namespace (\S+)',s,re.M)
 if ns:
  for name in re.findall(r'^theorem (\w+)',s,re.M):
   full=ns[1]+'.'+name;assert full in audited,full;new.append(full)
 candidates=[json.loads(p.read_text()) for p in receipts if json.loads(p.read_text())['exit_status']==0 and file.name in json.loads(p.read_text())['source_hashes']]
 assert any(r['source_hashes'][file.name]==sha(file) for r in candidates),file
before=(P/'BEk_004/stdout.log').read_bytes();after=(P/'BEk_100/stdout.log').read_bytes()
assert before==after
assert b'...' not in before and '…'.encode() not in before
for side,data in [('BEFORE',before),('AFTER',after)]:
 (P/f'BEk_{side}_KERNEL.lean.txt').write_bytes(data)
assert (P/'BEk_BEFORE_SOURCE.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()==(P/'BEk_AFTER_SOURCE.lean.txt').read_bytes()
ledger=json.loads((P/'BEk_recount.json').read_text());assert ledger['before']==ledger['after'];assert not any(ledger['delta'].values())
ledger_rows=json.loads((P/'BEk_ledger_rows.json').read_text())
for scope,label in [(None,'deduplicated actual plus non-alias deployment'),('actual antecedent','actual antecedent')]:
 selected=[r for r in ledger_rows if r['scope']==scope] if scope else [r for r in ledger_rows if r['scope']!='deployment alias']
 assert {c:sum(r['classification']==c for r in selected) for c in ['T','P','G','C']}==ledger['after'][label]['classes']
ledger['before_after_statement_sha256']=hashlib.sha256(before).hexdigest()
(P/'BEk_recount.json').write_text(json.dumps(ledger,indent=2)+'\n')
base=subprocess.check_output(['git','rev-parse','95b5c124b5^'],cwd=R,text=True).strip()
paths=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(x.startswith('evidence/l166-proof3-20261026/') or x.startswith('lean/BEk_') for x in paths)
assert all(not re.search(r'\.(?:olean|ir|elf|tar|gz|so|a|bin)$',x) for x in paths)
root_before=json.loads((P/'BEk_004/receipt.json').read_text())['deps_fingerprint']['selected_objects']['Rc10_Top.olean']
root_after=json.loads((P/'BEk_100/receipt.json').read_text())['deps_fingerprint']['selected_objects']['Rc10_Top.olean']
(P/'BEk_root_cache.json').write_text(json.dumps(dict(before=root_before,after=root_after,object_identical=root_before['sha256']==root_after['sha256'],validation='Fresh focused statement/axiom checks of the selected coherent cached root; not a root rebuild or frozen manifest replay'),indent=2)+'\n')
(P/'BEk_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
summary=dict(status='PASS; partial proof only; target not established',lean_invocations=len(rows),passed=passed,excluded_failures=len(rows)-passed,dependency_builds=0,distinct_statement_scope_reviews=77,kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in rows),maximum_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,new_theorems=new,standard_axiom_audit_lines=len(printed),before_after_kernel_identical=True,kernel_sha256=hashlib.sha256(before).hexdigest(),base_revision=base,root_delta=ledger['delta'],local_physical_association='OPEN',L166='OPEN')
(P/'BEk_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
