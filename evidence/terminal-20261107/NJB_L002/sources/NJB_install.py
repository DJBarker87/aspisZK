from pathlib import Path
import json,hashlib,subprocess
b=Path(__file__).resolve().parent;s=b/'NJB_src';patches=['NJB_KMX.patch','NJB_native.patch']
for patch in patches:subprocess.run(['git','apply','--check',str(b/patch)],cwd=s,check=True);subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True)
x=json.loads((b/'NJB_PATCH_FILES.json').read_text());manifest=json.loads((b/'NJB_STAGING_MANIFEST.json').read_text())
pins={q:r['sha256'] for q,r in manifest['files'].items()};overrides={q:r['after_sha256']for q,r in x.items()};overrides['crates/aspis-statement/src/pool_v1/NJB_terminal.rs']=hashlib.sha256((b/'NJB_terminal.rs.txt').read_bytes()).hexdigest()
for q,r in x.items():assert (s/q).read_bytes()==(s/q).read_bytes()[:-len(r['append'])]+r['append'].encode();assert hashlib.sha256((s/q).read_bytes()[:-len(r['append'])]).hexdigest()==r['before_sha256']
(b/'NJB_FROZEN_FILE_PINS.json').write_text(json.dumps(pins));(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(overrides))
print('scratch-only modules installed; native bodies unchanged')
