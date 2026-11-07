from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
xs=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
attempts=[x for x in xs if x.get('kind') in ['lean','link','audit','inspect','extract']]
assert len([x for x in attempts if x['kind']!='extract'])==40
assert len([x for x in attempts if x['kind']=='extract'])==2
pairs=0
for p in E.rglob('*.xz'):
 if p.with_suffix('.sha256').is_file():
  raw=lzma.decompress(p.read_bytes());assert sha(raw)==p.with_suffix('.sha256').read_text().strip(),str(p);pairs+=1
idx=json.loads((E/'NMX_INPUTS.json').read_text())
for h,row in idx['objects'].items():
 p=E/row['path'];assert sha(p.read_bytes())==row['archive_sha256'];raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==row['bytes']
for x in attempts:
 p=E/x['full_receipt'];assert sha(p.read_bytes())==x['full_receipt_sha256'];rc=json.loads(p.read_text());assert rc['attempt']==x['attempt']
 ad=json.loads((E/(x['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for n,h in rc['source_hashes'].items():assert idx['attempts'][x['attempt']][n]==h,(x['attempt'],n)
 if rc['exit_status']==0:
  for line in rc.get('print_axioms',[]):assert 'sorryAx' not in line,line
for row in json.loads((E/'NMX_AUDIT_C_PINS.json').read_text()):
 p=E/'NMX_native'/('NMX_'+Path(row['destination']).name+'.xz')
 assert sha(lzma.decompress(p.read_bytes()))==row['sha256']
raw=[]
for i in range(4):
 d=json.loads((E/f'NMX_audit/proof{i}/proof{i}.json').read_text());assert d['exit_status']==0
 for row in d['results']:
  assert set(row['walked_axioms']) <= {'propext','Classical.choice','Quot.sound'}
  assert row['equal'] is True
  raw.append(row)
expected=json.loads((E/'NMX_AUDIT_ROOTS.json').read_text())['records'];assert {x['root'] for x in raw}=={x['root'] for x in expected}
mods=json.loads((E/'NMX_EXPORT_MODULES.json').read_text())
for m in mods:
 s=(E/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option (maxRecDepth|maxHeartbeats)', '\n'.join(l for l in s.splitlines() if not l.lstrip().startswith('--'))),m
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
report=dict(status='PASS',formal_scopes=40,extraction_scopes=2,kani_runs=0,own_raw_roots=len(raw),compressed_sha_pairs=pairs,input_objects=len(idx['objects']),standard_axioms_only=True,collector_agreement=True,validated_source_modules=len(mods),export_complete=False,job_gate='INCOMPLETE',no_file_over20MB=True,security_target_established=False)
(E/'NMX_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
