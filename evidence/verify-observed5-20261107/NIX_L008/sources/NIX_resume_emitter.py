from pathlib import Path
import json,hashlib,subprocess,os
import NIX_stage as stage
B=Path(__file__).resolve().parent;D=B/'NIX_emitted/verify_observed';pins=json.loads((D/'NHR_PINS.json').read_text());doc=json.loads((D/'verify_observed.llbc').read_text());assert not doc['has_errors'];assert pins['charon_exit']==0
assert hashlib.sha256((D/'verify_observed.llbc').read_bytes()).hexdigest()==pins['llbc_sha256']
for n,h in stage.PINS.items():assert hashlib.sha256((stage.TOOLROOT/n).read_bytes()).hexdigest()==h
inventory=json.loads((D/'NHR_DECLARATIONS.json').read_text());matched=[]
for boundary in pins['opacity']:
 if boundary['path']=='crate::verifier::mark':continue
 parts=boundary.get('selector',boundary['path']).replace('crate::','aspis_r1_cost_probe::').split('::')
 hits=[f for f in inventory if len(parts)==len(f['name']) and all(p=='_' or p==(e['Ident'][0] if 'Ident' in e else '_') for p,e in zip(parts,f['name']))]
 assert hits and all(f['body_kind'] in ('Opaque',['Opaque']) for f in hits),boundary
 matched.append(dict(boundary=boundary,matches=hits))
name=lambda f:'::'.join(e['Ident'][0] if 'Ident'in e else '_' for e in f['name'])
for n in ['aspis_r1_cost_probe::r1_semantic::verify_observed','aspis_r1_cost_probe::r1_semantic::mark']:
 hit=next(f for f in inventory if name(f)==n);assert hit['body_kind']==['Structured']
# More concrete body retained: actual local mark, not a replacement opaque template.
record=dict(one_charon_launch='NIX_E001',llbc_sha256=pins['llbc_sha256'],root=pins['root'],validated_opacity=matched,transparent_mark='aspis_r1_cost_probe::r1_semantic::mark',command=pins['aeneas_command'],cargo_target_dir=os.environ['CARGO_TARGET_DIR'])
(B/'NIX_EMISSION_RESUME.json').write_text(json.dumps(record,indent=2))
r=subprocess.run(pins['aeneas_command'],cwd=B)
record.update(exit=r.returncode,outputs={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (D/'raw').rglob('*') if p.is_file()})
(B/'NIX_EMISSION_RESUME.json').write_text(json.dumps(record,indent=2));raise SystemExit(r.returncode)
