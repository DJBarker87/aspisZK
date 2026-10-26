"""Offline receipt/source/axiom/scope/recount checks; no compilation or launcher changes."""
from pathlib import Path
import hashlib,json,re,subprocess,collections
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(f.read_text()) for f in sorted(P.glob('ARU_*/receipt.json'))]
assert len(rs)==100 and {r['attempt'] for r in rs}=={f'ARU_{i:03}' for i in range(1,101)}
allowed={'propext','Classical.choice','Quot.sound'};latest={};passed=[];failed=[]
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command'] and int(r['swaps'])==0
 assert r['source_revision'] and r['deps_fingerprint']
 for f,h in r['source_hashes'].items():assert sha(P/r['attempt']/'sources'/f)==h
 if r['exit_status']==0:
  passed.append(r)
  for line in r['print_axioms']:
   assert 'sorryAx' not in line,(r['attempt'],line)
   if 'depends on axioms:' in line:
    actual=set(re.findall(r'\[([^]]*)\]',line,re.S)[-1].replace('\n','').replace(' ','').split(','))
    assert actual<=allowed,(r['attempt'],line)
  latest.update(r['source_hashes'])
 else:failed.append(r)
for p in (R/'lean').glob('ARU_*.lean'):
 assert latest.get(p.name)==sha(p),p.name
 source=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);source=re.sub(r'--[^\n]*','',source)
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',source),p.name
final=next(r for r in rs if r['attempt']=='ARU_099');assert final['exit_status']==0
printed='\n'.join(final['print_axioms'])
for name in json.loads((P/'ARU_THEOREMS.json').read_text()):assert "'"+name+"'" in printed,name
before=(P/'ARU_067/stdout.log').read_bytes();after=(P/'ARU_100/stdout.log').read_bytes()
assert before==after and '⋯' not in before.decode()
(P/'ARU_BEFORE_KERNEL.lean.txt').write_bytes(before);(P/'ARU_AFTER_KERNEL.lean.txt').write_bytes(after)
assert (P/'ARU_BEFORE_SOURCE.lean.txt').read_bytes()==(P/'ARU_AFTER_SOURCE.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
ledger=json.loads((P/'ARU_LEDGER_DELTA.json').read_text());assert ledger['before']==ledger['after']
assert not ledger['removed'] and not ledger['added'] and not ledger['reclassified']
for scope in ['actual antecedent','deployment only','deployment alias']:
 rows=[r for r in ledger['rows'] if r['scope']==scope];c=collections.Counter(r['classification'] for r in rows)
 assert ledger['before'][scope]==dict(rows=len(rows),classes={k:c[k] for k in 'TPGC'})
assert ledger['before']['actual antecedent']['classes']=={'T':83,'P':12,'G':13,'C':0}
assert ledger['before']['deduplicated actual plus non-alias deployment']['classes']=={'T':89,'P':16,'G':13,'C':0}
assert ledger['aliases']=={'L185':'L159'}
assert sha(R/ledger['baseline_path'])==ledger['baseline_sha256']
changed=subprocess.check_output(['git','diff','--name-only','06b9715c208c49fdd01ef646a06d3530880171ad'],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/ARU_') or p.startswith('evidence/account-rejoin6-20261026/') for p in changed)
assert all(not p.endswith(('.olean','.elf','.tar','.gz','.bin')) for p in changed)
for pin in json.loads((P/'ARU_FIXTURE_PREDECESSORS.json').read_text()):
 data=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']],cwd=R)
 assert hashlib.sha256(data).hexdigest()==pin['sha256']
host=json.loads((P/'ARU_HOST_MANIFEST.json').read_text())
for item in host:
 assert sha(R/'lean'/item['module'])==item['source_sha256']
 assert item['object_sha256'] and item['object_bytes']>0
summary=dict(status='PASS',lean_attempts=len(rs),passed=len(passed),failed_excluded=len(failed),kani_runs=0,dependency_builds=0,new_theorems=len(json.loads((P/'ARU_THEOREMS.json').read_text())),actual_top_removed=0,wall_seconds=sum(r['wall_seconds'] for r in rs),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=0,failed_attempts=[r['attempt'] for r in failed],excluded_exploratory_diagnostic='ARU_075; finishOwners is not L181; source retained only in evidence',final_audit={k:final[k] for k in ['attempt','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},scope='Focused cached closure and distinct statement audits, not frozen release replay')
(P/'ARU_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'ARU_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
print(json.dumps({k:v for k,v in summary.items() if k!='final_audit'},indent=2))
