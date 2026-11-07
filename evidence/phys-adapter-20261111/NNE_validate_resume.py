"""Read-only evidence/source validation, no prover replay."""
from pathlib import Path
import json,hashlib,lzma,ast,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
records=[json.loads(l) for l in (E/'NNE_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=[x for x in records if x.get('kind') in ['lean','link','audit','inspect']]
assert len(scopes)==90 and len({x['attempt'] for x in scopes})==90
for x in scopes:
 p=E/x['full_receipt'];assert sha(p.read_bytes())==x['full_receipt_sha256']
 a=json.loads((E/(x['attempt']+'-admission.json')).read_text())
 assert a['exit']==0 and a['reservation']['allowed'] is True
 receipt=json.loads(p.read_text());assert receipt['exit_status']==x['exit_status']
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
pairs=0
for p in E.rglob('*.sha256'):
 q=Path(str(p).removesuffix('.sha256')+'.xz')
 if q.exists():assert sha(lzma.decompress(q.read_bytes()))==p.read_text().strip();pairs+=1
idx=json.loads((E/'NNE_INPUTS.json').read_text())
for h,x in idx['objects'].items():
 p=E/x['path'];assert sha(p.read_bytes())==x['archive_sha256']
 raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==x['bytes']
mods=json.loads((E/'NNE_RESUME_MODULES.json').read_text())
source_hashes={}
for m in mods+['NNE_RESUME_COMBINED_IMPORT']:
 h=sha((E/(m+'.lean')).read_bytes());source_hashes[m]=h
 assert any(x.get('module')==m and x['exit_status']==0 and h in x['source_hashes'].values() for x in scopes)
for p in E.glob('NNE_*.py'):ast.parse(p.read_text(),filename=str(p))
a=json.loads((E/'NNE_RESUME_AUDIT.json').read_text())
assert len(a['roots'])==59
for row in a['roots']:assert row['equal'] and set(row['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
ret=json.loads((E/'NNE_RETENTION.json').read_text());assert ret['deletions']==0 and ret['aeneas_files_verified']>=239
changed=subprocess.check_output(['git','diff','--name-only','1422835d3c4'],text=True).splitlines()
assert all(p.startswith('evidence/phys-adapter-20261111/NNE_') for p in changed)
result=dict(status='PASS',scope_count=len(scopes),resume_scopes=len(scopes)-47,kani=0,extraction=0,
 axioms=a['standard_axioms'],new_roots=59,archived_inputs=len(idx['objects']),compressed_sha_pairs=pairs,
 current_source_hashes=source_hashes,only_assigned_paths_changed=True,no_file_over_20MB=True,
 host_export='NNE_EXPORT.json',retention=ret,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NNE_RESUME_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['current_source_hashes','retention']}))
