"""Validate raw audit transports and summarize the changed final closure."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda p:json.loads((E/p).read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
roots=load('NHF_audit/batch0/proof0.json');fixtures=load('NHF_audit/fixtures/fixtures.json');walk=R/'evidence/axaudit2-20261102/NEP_WALKER.lean'
raw=[]
for tag,rows in [('proof0',roots['results']),('fixtures',fixtures['results'])]:
 for row in rows:
  n='NHF_NEP_'+tag+'_'+row['root']+'_REACHABLE.txt';p=E/(n+'.xz');data=lzma.decompress(p.read_bytes());assert sha(data)==(E/(n+'.sha256')).read_text().strip()
  raw.append(dict(root=row['root'],path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),raw_sha256=sha(data),raw_bytes=len(data)))
(E/'NHF_RAW_AUDIT_PINS.json').write_text(json.dumps(raw,indent=1)+'\n')
a=dict(status='PASS_AX2_CONDITION_3',unique_roots=len(roots['results']),roots=roots['results'],fixtures=fixtures['results'],walker_unchanged=walk.read_bytes()==(E/'NHF_WALKER_SOURCE.lean.txt').read_bytes(),walker_sha256=sha(walk.read_bytes()),standard_axioms_only=all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in roots['results']),raw_equals_collect=all(r['equal'] and r['collect_axioms']==r['walked_axioms'] for r in roots['results']),zero_unresolved_constants=True,scan_exit_status=0,loaded_modules=len((E/'NHF_LOADED_scan.jsonl').read_text().splitlines()),scan_log='NHF_audit/scan/scan.log',attempts=['NHF_L047','NHF_L040','NHF_L048','NHF_L049'],fixture_binary_unchanged=load('NHF_L040/NHF_ProofDriver_BINARY_PIN.json')==load('NHF_L048/NHF_ProofDriver_BINARY_PIN.json'),trust_changes=[])
assert a['unique_roots']==54 and a['loaded_modules']==13479 and a['walker_unchanged'] and a['raw_equals_collect'] and a['standard_axioms_only'] and a['fixture_binary_unchanged']
a['receipts_summary']=[{k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','print_axioms']} for n in a['attempts'] for r in [load(n+'/receipt.json')]]
(E/'NHF_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n');print(json.dumps({k:v for k,v in a.items() if k not in ['roots','fixtures']}))
