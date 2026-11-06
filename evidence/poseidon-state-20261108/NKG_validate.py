from pathlib import Path
import hashlib,json,lzma,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run(['python3',str(E/'NKG_sourcecheck.py')],check=True,capture_output=True)
subprocess.run(['python3',str(E/'NKG_finalize.py')],check=True,capture_output=True)
assert subprocess.run(['git','diff','--check'],capture_output=True).returncode==0
large=[str(p.relative_to(E))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20000000];assert not large,large
compressed=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256');assert q.exists(),p
 assert sha(lzma.open(p).read())==q.read_text().strip(),p
 compressed+=1
inventory=json.loads((E/'NKG_PROOF_INVENTORY.json').read_text())
for m,pin in inventory['modules'].items():
 p=E/'NKG_lean'/f'{m}.lean';assert sha(p.read_bytes())==pin['source_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),m
 assert not re.search(r'^theorem ',p.read_text(),re.M) or '#print axioms'in p.read_text(),m
 assert p.read_bytes()==(E/pin['attempt']/'sources/NKG_lean'/p.name).read_bytes(),m
export=json.loads((E/'NKG_L055_validation/NKG_EXPORT.json').read_text())
closure=json.loads(lzma.open(E/'NKG_L055_validation/NKG_CLOSURE_PINS.json.xz').read())
assert closure['variants']==0 and closure['modules']==15995
assert len({r['module']for r in closure['selected_objects']if r['module'].startswith('NKG_')})==32
assert len(export['files'])==len([r for r in closure['selected_objects']if r['module'].startswith('NKG_')])
assert not list(E.rglob('__pycache__'))
res=dict(status='PASS',source_association=True,accepted_modules=len(inventory['modules']),source_snapshots=True,compressed_sha_pairs=compressed,no_large_file=True,standard_axioms_gate=True,coherent_export=True,shipped_unchanged=True,own_validator_only=True)
(E/'NKG_VALIDATION.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
