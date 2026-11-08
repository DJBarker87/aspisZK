from NMX_formal import *
script='''from pathlib import Path
import json,hashlib,lzma
b=Path.cwd();manifest=json.loads((b/'NMX_R9_EXPORT.json').read_text());pins=json.loads(lzma.decompress((b/'NMX_R9_CLOSURE_PINS.json.xz').read_bytes()))
checked=0
for row in manifest['files']:
 p=Path(row['path']);assert p.is_relative_to(b/'NMX_exports_stage241_20261111'),str(p)
 assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 checked+=1
for row in pins['objects']:
 if row['module'].startswith('RSL_'):assert Path(row['path']).is_relative_to(b/'NMX_R3_canonical_objects'),row
result=dict(status='PASS',checked_export_files=checked,loaded_modules=manifest['loaded_modules'],loaded_objects=manifest['loaded_objects'],canonical_revision=3,missing=0,drifted=0,deletions=0)
(b/'NMX_R9_RETAINED_CHECK.json').write_text(json.dumps(result,indent=1)+'\\n');print(json.dumps(result))
'''
r=run('NMX_L1392','inspect','retained_readback_r9',['python3','NMX_R9_verify_retained_host.py'],{'NMX_R9_verify_retained_host.py':script})
assert r['exit_status']==0
z=ssh('cat '+B+'/NMX_R9_RETAINED_CHECK.json');assert z.returncode==0
(E/'NMX_R9_RETAINED_CHECK.json').write_text(z.stdout)
