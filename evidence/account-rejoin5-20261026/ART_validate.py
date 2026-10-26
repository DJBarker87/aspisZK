"""Offline ART proof/receipt/budget and unchanged-root ledger validation."""
from pathlib import Path
import hashlib,json,re,subprocess,collections
P=Path(__file__).resolve().parent; R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(f.read_text()) for f in sorted(P.glob('ART_*/receipt.json'))]
assert len(receipts)==100 and len({r['attempt'] for r in receipts})==100
passed=[r for r in receipts if r['exit_status']==0];failed=[r for r in receipts if r['exit_status']!=0]
allowed={'propext','Classical.choice','Quot.sound'}; latest={}
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
  latest.update(r['source_hashes'])
for p in (R/'lean').glob('ART_*.lean'):
 assert latest.get(p.name)==sha(p),p.name
 s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',s),p.name
final=next(r for r in receipts if r['attempt']=='ART_099');assert final['exit_status']==0
printed='\n'.join(final['print_axioms'])
for t in json.loads((P/'ART_THEOREMS.json').read_text()):assert "'"+t+"'" in printed,t
before=(P/'ART_072/stdout.log').read_bytes();after=(P/'ART_100/stdout.log').read_bytes()
assert before==after and '⋯' not in before.decode()
(P/'ART_BEFORE_KERNEL.lean.txt').write_bytes(before);(P/'ART_AFTER_KERNEL.lean.txt').write_bytes(after)
assert (P/'ART_BEFORE_SOURCE.lean.txt').read_bytes()==(P/'ART_AFTER_SOURCE.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
ledger=json.loads((P/'ART_LEDGER_DELTA.json').read_text()); assert ledger['before']==ledger['after']
assert not ledger['removed'] and not ledger['added'] and not ledger['reclassified']
for scope in ['actual antecedent','deployment only','deployment alias']:
 rows=[r for r in ledger['rows'] if r['scope']==scope];c=collections.Counter(r['classification'] for r in rows)
 assert ledger['before'][scope]==dict(rows=len(rows),classes={k:c[k] for k in 'TPGC'})
assert ledger['before']['actual antecedent']['classes']=={'T':83,'P':12,'G':13,'C':0}
assert ledger['before']['deduplicated actual plus non-alias deployment']['classes']=={'T':89,'P':16,'G':13,'C':0}
assert ledger['aliases']=={'L185':'L159'}
changed=subprocess.check_output(['git','diff','--name-only','d516d96550'],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/ART_') or p.startswith('evidence/account-rejoin5-20261026/') for p in changed)
assert all(not p.endswith(('.olean','.elf','.tar','.gz','.bin')) for p in changed)
for pin in json.loads((P/'ART_FIXTURE_PREDECESSORS.json').read_text()):
 data=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']],cwd=R)
 assert hashlib.sha256(data).hexdigest()==pin['sha256']
summary=dict(status='PASS',lean_attempts=len(receipts),passed=len(passed),failed_excluded=len(failed),kani_runs=0,dependency_builds=0,new_theorems=len(json.loads((P/'ART_THEOREMS.json').read_text())),actual_top_removed=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,failed_attempts=[r['attempt'] for r in failed],final_audit={k:final[k] for k in ['attempt','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},scope='Focused coherent cached import/axioms/statement checks, no frozen release rebuild')
(P/'ART_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'ART_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps({k:v for k,v in summary.items() if k!='final_audit'},indent=2))
