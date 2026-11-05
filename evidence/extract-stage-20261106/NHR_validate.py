"""Compile-free verification of the committed NHR artifact/receipt packet."""
from pathlib import Path
import base64,hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def data(p):
 if p.exists():return p.read_bytes()
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes())
 assert sha(raw)==Path(str(p)+'.sha256').read_text().strip()
 return raw
pins=json.loads((E/'NHR_PINS.json').read_text());manifest=json.loads((E/'NHR_STAGING_MANIFEST.json').read_text())
assert sha((E/'NHR_stage.py').read_bytes())==pins['stager_sha256']
assert sha((E/'NHR_parameterize.py').read_bytes())==pins['parameterizer_sha256']
assert sha((E/'NHR_STAGING_MANIFEST.json').read_bytes())==pins['manifest_sha256']
assert sha((E/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes())==pins['payload_sha256']
raw=lzma.decompress((E/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes());assert sha(raw)==(E/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
payload=json.loads(raw);assert set(payload)==set(manifest['files'])
for name,info in manifest['files'].items():
 b=base64.b64decode(payload[name]);assert sha(b)==info['sha256'] and len(b)==info['bytes']
 oid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert oid==info['git_blob']
 actual=subprocess.check_output(['git','rev-parse',manifest['revision']+':'+name],cwd=E,text=True).strip();assert actual==oid
assert len(pins['emissions'])==4
for row in pins['emissions']:
 base=E/row['evidence'];ep=json.loads((base/'NHR_PINS.json').read_text())
 assert sha((base/'NHR_PINS.json').read_bytes())==row['pins_sha256']
 assert ep['charon_exit']==ep['aeneas_exit']==ep['exit']==0
 assert ep['lock_before']==ep['lock_after']==pins['frozen_lock_sha256']
 assert sha(data(base/(row['function']+'.llbc')))==row['llbc_sha256']
 for path,info in row['raw_files'].items():assert sha((E/path).read_bytes())==info['sha256']
 for item in ep['validated_opacity']:
  assert item['matches']
  assert all(x['body_kind'] in ('Opaque',['Opaque']) for x in item['matches'])
 graph=json.loads((base/'NHR_GRAPH_CHECK.json').read_text());assert graph['graph_matches_frozen'] and not graph['added'] and not graph['edge_errors']
for p,h in pins['compiled_sources'].items():
 s=(E/p).read_text();assert sha(s.encode())==h
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b',re.sub(r'--[^\n]*','',s))
entries=[json.loads(l) for l in (E/'NHR_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(entries)==len({r['attempt'] for r in entries})==18
for entry in entries:
 a=entry['attempt'];r=json.loads(data(E/a/'receipt.json'));ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0' and r['exit_status']==(1 if a in ['NHR_E001','NHR_E003'] else 0)
 for name,h in r['source_hashes'].items():assert sha(data(E/a/'sources'/name))==h
 if r['kind']=='lean':
  assert r['exit_status']==0
  for line in r['print_axioms']:
   assert 'sorryAx' not in line
   if 'depends on axioms:' in line:assert set(re.search(r'\[([^]]*)\]',line)[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'}
combined=json.loads((E/'NHR_L009/receipt.json').read_text());assert len(combined['print_axioms'])==5
assert json.loads((E/'NHR_final_preflight/NHR_GRAPH_CHECK.json').read_text())['graph_matches_frozen']
assert json.loads((E/'NHR_SHIPPED_IDENTITY.json').read_text())['unchanged']
assert sha((E/'NHR_SEED.json').read_bytes())==pins['seed_sha256']
assert sha((E/'NHR_EXPORT.json').read_bytes())==pins['export_sha256']
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
print('PASS: frozen payload/Git objects, four emissions, 18 receipts, all admissions/caps, standard printed axioms, export pins')
