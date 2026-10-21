from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (r/'SHA256SUMS').read_text().splitlines():
 h,name=line.split(maxsplit=1);assert sha(r/name)==h,name
p=r/'receipts';w=p/'standing-runner-v2'
m=json.loads((w/'standing-command-manifest.json').read_text());s=json.loads((w/'standing-result-v2.json').read_text())
artifact='40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0'
assert m['count']==len(m['commands'])==30
assert s['all_exit_zero'] and len(s['rows'])==30
assert m['candidate_artifact_sha256']==s['candidate_artifact_sha256']==artifact
assert s['manifest_sha256']==sha(w/'standing-command-manifest.json')
assert {x['name'] for x in m['commands']}=={x['name'] for x in s['rows']}
for x in s['rows']:
 q=w/'standing-evidence-v2'/x['name']
 j=json.loads((q/'receipt.json').read_text())
 assert j['exit_status']==0 and not j['timed_out']
 assert j['candidate_artifact_sha256']==artifact and j['swap_current_bytes']==0
 assert j['limits']=={'memory.high':'2147483648','memory.max':'4294967296','memory.swap.max':'0'}
 assert (q/'command.json').is_file() and (q/'time.log').is_file()
fixtures=list((p/'work/runs').glob('cu-*/evidence.json'));assert len(fixtures)==6
stage=[];settle=[]
for f in fixtures:
 j=json.loads(f.read_text());e=j['execution']
 assert j['artifacts']['r1_cost_probe_verifier']['sha256']==artifact
 assert e['error'] is None and e['stage1_error'] is None and e['outcome']=='accepted'
 assert e['declared_compute_unit_limit']==e['runtime_compute_limit']==1400000
 assert not e['runtime_limit_is_diagnostic_override'] and j['fixture']['proof_bytes']==57607
 assert e['stage1_compute_units']<1400000 and e['compute_units']<1400000
 stage.append(e['stage1_compute_units']);settle.append(e['compute_units'])
assert max(stage)==1210100 and max(settle)==1189265
ids=json.loads((p/'id-slot-check/identity-task/receipts/identity/identity.json').read_text())
assert ids['text_identical'] and ids['only_two_data_slots'] and ids['artifacts']['default']['sha256']==artifact
assert len(ids['slots'])==2 and all(x['bytes']==32 for x in ids['slots'])
assert not any('keypair' in x.name or x.suffix in {'.so','.olean','.bin'} for x in r.rglob('*') if x.is_file())
print('PASS: retained30 native commands; six current-format fixtures; artifact/text identity; finite measurements only')
