from pathlib import Path
import json,hashlib
B=Path.cwd();load=lambda n:json.loads((B/n).read_text());required=['NJG_CUTS.md','NJG_STUBS.md','NJG_CERTIFICATES.md','NJG_CLOSED.json','NJG_LEDGER_DELTA.json','NJG_AUDIT.json','NJG_COMBINED_IMPORT.lean','NJG_FAILING_STEP.md','NJG_HANDOFF.md','NJG_REMAINING.md','NJG_ATTEMPTS.jsonl','NJG_ROOT_INVENTORY.md','NJG_PRINTED_ROOTS.md']
assert all((B/n).is_file() and (B/n).stat().st_size<20_000_000 for n in required)
assert load('NJG_CLOSED.json')['functions']==[] and not load('NJG_CLOSED.json')['security_target_established']
x=load('NJG_LEDGER_DELTA.json');assert x['before_counts']==x['after_counts']=={'CLOSED':432,'OPEN':167} and x['changed_rows']==[]
x=load('NJG_AUDIT.json');assert x['combined_audits_used']==2 and x['final_gate']['roots']==100 and x['final_gate']['dangling']==0
assert x['native_validation']['status']=='PASS_LOCAL_SUPPORT_ONLY'
for m in load('NJG_MODULES.json'):
 p=B/'NJG_generated'/(m['module']+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
lines=[json.loads(s) for s in (B/'NJG_ATTEMPTS.jsonl').read_text().splitlines()];assert len(lines)==127 and len({r['attempt'] for r in lines})==127
assert all(r.get('source_revision') and 'exit_status' in r and 'wall_seconds' in r and 'peak_rss_kib' in r and 'swaps' in r and 'print_axioms' in r for r in lines)
assert load('NJG_L099/receipt.json')['exit_status']==0
out=dict(status='PASS_FINAL_ARTIFACTS_ONLY',required_files=len(required),support_modules=len(load('NJG_MODULES.json')),completed_predecessor_attempts=len(lines),this_attempt='NJG_L100',new_closed_rows=0,security_target_established=False,hashes={n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in required})
(B/'NJG_ARTIFACT_CHECK.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='hashes'}))
