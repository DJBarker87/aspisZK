"""Offline ARS receipt, source, budget, standard-axiom and ledger checks."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent; R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('ARS_*/receipt.json'))]
assert len(receipts)==100
assert len({r['attempt'] for r in receipts})==100
assert not (P/'ARS_003/receipt.json').exists()
passed=[r for r in receipts if r['exit_status']==0];failed=[r for r in receipts if r['exit_status']!=0]
allowed={'propext','Classical.choice','Quot.sound'};latest={}
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert r['source_revision'] and r['deps_fingerprint'] and int(r['swaps'])==0
 for f,h in r['source_hashes'].items():assert sha(P/r['attempt']/'sources'/f)==h
 if r['exit_status']==0:
  for s in r['print_axioms']:
   assert 'sorryAx' not in s
   if 'depends on axioms:' in s:
    axioms=set(re.findall(r'\[([^]]*)\]',s,re.S)[-1].replace('\n','').replace(' ','').split(','))
    assert axioms<=allowed,(r['attempt'],s)
  for f,h in r['source_hashes'].items():latest[f]=h
sources=list((R/'lean').glob('ARS_*.lean'))
for p in sources:
 assert latest[p.name]==sha(p),p.name
 s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
 s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',s),p.name
final=next(r for r in receipts if r['attempt']=='ARS_101')
assert final['exit_status']==0
printed='\n'.join(final['print_axioms'])
for t in json.loads((P/'ARS_THEOREMS.json').read_text()):assert "'"+t+"'" in printed,t
assert (P/'ARS_BEFORE_SOURCE.lean.txt').read_bytes()==(P/'ARS_AFTER_SOURCE.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
assert (P/'ARS_BEFORE_KERNEL.lean.txt').read_bytes()==(P/'ARS_AFTER_KERNEL.lean.txt').read_bytes()
assert '⋯' not in (P/'ARS_AFTER_KERNEL.lean.txt').read_text()
ledger=json.loads((P/'ARS_LEDGER_DELTA.json').read_text())
assert ledger['before']==ledger['after'] and not ledger['removed'] and not ledger['added'] and not ledger['reclassified']
assert ledger['before']['actual antecedent']['classes']=={'T':83,'P':12,'G':13,'C':0}
assert ledger['before']['deduplicated actual plus non-alias deployment']['classes']=={'T':89,'P':16,'G':13,'C':0}
changed=subprocess.check_output(['git','diff','--name-only','5da6b7b01e6ef5f5e69ebf4939c44c78af2b2e30'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/ARS_') or p.startswith('evidence/account-rejoin4-20261026/') for p in changed)
output=dict(status='PASS',lean_attempts=len(receipts),prelaunch_only=['ARS_003'],passed=len(passed),failed_excluded=len(failed),kani_runs=0,dependency_builds=52,new_theorems=48,actual_top_removed=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,final_audit={k:final[k] for k in ['attempt','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},scope='Focused coherent import/axioms audit; no package or frozen manifest replay; no release claim')
(P/'ARS_VALIDATION.json').write_text(json.dumps(output,indent=2)+'\n')
(P/'ARS_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps({k:v for k,v in output.items() if k!='final_audit'},indent=2))
