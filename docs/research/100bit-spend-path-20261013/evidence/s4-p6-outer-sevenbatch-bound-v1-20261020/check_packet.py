from pathlib import Path
import hashlib,json
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert len(m['modules'])==1
x=m['modules'][0]
for key in ['source','receipt','preflight','command','time_log','lean_log']:
 f=p/x[key]; assert f.is_file(), key
assert sha(p/x['source'])==x['source_sha256']
r=json.loads((p/x['receipt']).read_text())
assert r['exit_status']==0 and r['source_sha256']==x['source_sha256']
assert r['object_sha256']==x['object_sha256']
assert r['swaps']==0
assert x['axioms']==['propext','Classical.choice','Quot.sound']
for name,d in m['direct_import_source_map'].items():
 f=(p/d['source']).resolve()
 assert f.is_file(), (name,str(f))
 assert sha(f)==d['source_sha256'], name
assert (p/'dependencies/S4FromFnP6Loop0ArrayOpIrrelevanceV1.lean').is_file()
assert not list(p.rglob('*.olean'))
print('PASS: source-only packet, exact source/object receipts, direct source pins, zero swap, standard axioms')
