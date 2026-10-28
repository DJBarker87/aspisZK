from pathlib import Path
import json,time,hashlib
E=Path(__file__).resolve().parent
load=lambda p:json.loads((E/p).read_text())
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
for m,h in pins.items():
 r=load('build-'+m+'/comparison.json');assert r['matches'] and r['sha256']==r['expected']==h
assert 'rustc 1.94.1 ' in (E/'build-client/rustc-vV.txt').read_text()
assert 'e408947bfd200af42db322daf0fadfe7e26d3bd1' in (E/'build-client/rustc-vV.txt').read_text()
r=load('fixture-comparison.json');assert r['passed'] and r['deterministic_passed']
for row in r['comparisons']:
 assert row['deterministic_result_records_byte_identical'] and row['ledger_files_byte_identical'] and all(x['byte_identical'] for x in row['files'].values())
s=load('combined/corpus-6000/pipeline-final.json');assert s['passed'] and s['complete'] and s['completed_pairs']==1000 and s['fully_executed_proof_pairs']==600 and s['rejected_prefix_pairs']==100 and s['oracle_logged_pairs']==4
assert {r['coin'] for r in s['cases']}==set(range(6000,7000))
resources=s['final_resources'];assert resources['pids_events'].get('max',0)==0 and resources['memory_events'].get('oom_kill',0)==0 and resources['swap_current_bytes']==0
r=load('combined/record-ledger-audit.json');assert r['passed'] and r['records']==r['canonical_records_byte_identical']==r['ledger_pairs_identical']==1000
receipts=[]
for p in E.rglob('receipt/receipt.json'):
 r=json.loads(p.read_text());assert r['exit_status']==0 and r['swaps']==0,(p,r)
 assert int(r['limits']['memory.high'])==6*2**30 and int(r['limits']['memory.max'])==8*2**30 and r['limits']['memory.swap.max']=='0' and r['limits']['pids.max']=='64',p
 assert 'N/A' in r['print_axioms'] and r['source_revision'] in {'82566acdfb488183022f41ac564c11df22c9404f','c57a344726745387efb38d1571d885c69ce829ee'}
 receipts.append(dict(path=str(p.relative_to(E)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],print_axioms=r['print_axioms']))
for f in ['source-identity.json','control-source-identity.json']:assert load(f)['passed']
(E/'stage-a-validation.json').write_text(json.dumps(dict(utc=time.time(),passed=True,receipts=receipts,cohort=dict(pairs=1000,complete_proof_pairs=600,rejected_prefix_pairs=100,oracle_log_pairs=4),print_axioms='N/A: no Lean',scope='Evidence consistency and recorded caps; no native workload rerun'),indent=2)+'\n')
print('Stage A validated:',len(receipts),'successful capped receipts, all 1000 pairs and canonical ledger audit')
