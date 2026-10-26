"""Validate and index the complete 100-attempt evidence, without recompilation."""
from pathlib import Path
import json,re,hashlib,subprocess,csv
root=Path.cwd();p=root/'evidence/pv-runjoin6-20261026'
rows=sorted((json.loads(f.read_text()) for f in p.glob('receipt-*.json')),key=lambda r:r['attempt'])
assert [r['attempt'] for r in rows]==list(range(26800,26900)), 'budget not yet complete'
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 source=p/r['source_snapshot'];assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
 deps={k:v['sha256'] for k,v in r['direct_dependencies_before'].items()}
 r['deps_fingerprint']=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
 if r['accepted']:
  for line in r['axioms']:
   match=re.search(r'depends on axioms: \[([^]]*)\]',line,re.S)
   if match: assert set(map(str.strip,match[1].replace('\n',' ').split(',')))<=allowed,line
(p/'attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
fields=['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','deps_fingerprint','accepted','print_axioms']
with (p/'receipt-index.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=fields,delimiter='\t');w.writeheader()
 for r in rows:w.writerow({**{k:r[k] for k in fields[:-1]},'print_axioms':'; '.join(x.replace('\n',' ') for x in r['axioms'])})
current=[]
formal=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for source in sorted(formal.glob('PV_RunJoin_Trust*.lean')):
 target='R1Z/'+source.stem;proofs=[r for r in rows if r['target']==target and r['accepted']]
 assert proofs,target
 r=proofs[-1];sha=hashlib.sha256(source.read_bytes()).hexdigest();assert sha==r['source_sha256'],target
 current.append(dict(target=target,attempt=r['attempt'],sha256=sha,axioms=r['axioms']))
(p/'accepted-source-audit.json').write_text(json.dumps(current,indent=2)+'\n')
budget=dict(lean_attempts=len(rows),lean_accepted=sum(r['accepted'] for r in rows),lean_failed=sum(not r['accepted'] for r in rows),lean_proof_statement_development=22,lean_split_cached_handoff_audits=77,lean_final_cached_audit=1,remaining_lean=0,kani_runs=11,kani_successful_value_cuts=10,kani_native_foreign_rejection=1,remaining_kani=0,max_peak_rss_bytes=max(r['peak_rss_bytes'] or 0 for r in rows),swaps=sum(r['swaps'] or 0 for r in rows),full_source_manifest_replay=False,target_established=False)
(p/'budget.json').write_text(json.dumps(budget,indent=2)+'\n')
(p/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline','87a332c140..HEAD'],text=True))
assert not subprocess.check_output(['git','diff','87a332c140','--name-only','--','crates','programs'],text=True)
published=['SourceSelectionContract','SelectedAdmission','NativeSelectedInputs','InstalledTransport']
paths=['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_'+n+'.lean' for n in published]
assert not subprocess.check_output(['git','diff','87a332c140','--',*paths],text=True)
print(json.dumps(budget,indent=2))
