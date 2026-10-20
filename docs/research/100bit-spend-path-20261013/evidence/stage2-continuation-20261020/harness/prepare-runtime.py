#!/usr/bin/env python3
"""Prepare a fresh, non-overwriting gate namespace after a source change."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path(__file__).resolve().parents[1];tag=sys.argv[1];d=E/'harness'/tag;d.mkdir(exist_ok=False)
for p in (E/'harness/r2').rglob('*'):
 if p.is_file():
  q=d/p.relative_to(E/'harness/r2');q.parent.mkdir(exist_ok=True,parents=True);q.write_text(p.read_text().replace('harness-r2','harness-'+tag).replace('runs-r2','runs-'+tag).replace('stack-r2','stack-'+tag).replace('cu-r2','cu-'+tag).replace('r2-',''+tag+'-').replace('publication-r2','publication-'+tag))
p=E/'pins/build-inputs.json';j=json.loads(p.read_text());j['base_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for f in j['files']:f['sha256']=hashlib.sha256(Path(f['path']).read_bytes()).hexdigest()
p.write_text(json.dumps(j,indent=2)+'\n')
