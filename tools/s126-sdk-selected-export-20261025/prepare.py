#!/usr/bin/env python3
"""New source-selected caller terms, over TWO immutable raw-data layers."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-selected-cut-export-20261025';P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bases=[];names=set();transports=[]
for rel,constant_file in [('sdk-current-export-20261024','constants.jsonl'),('sdk-current-incremental-20261024','constants-incremental.jsonl')]:
 release=json.loads((E/rel/'release.json').read_text());d=Path(release['location']);assert sha(d/'manifest.json')==release['manifest_sha256'];m=json.loads((d/'manifest.json').read_text());rows=[json.loads(l) for l in (d/constant_file).read_text().splitlines()]
 for row in rows:assert row['name'] not in names;names.add(row['name'])
 files=[f for f in m['files'] if f['relative'].startswith('transport/')]
 bases.append(dict(location=str(d),manifest_sha256=release['manifest_sha256'],constant_file=constant_file,constant_file_sha256=sha(d/constant_file),constants=len(rows),transport_modules=len(files),files=files))
 for f in files:
  path=d/f['relative'];assert sha(path)==f['sha256'] and not path.is_symlink();transports.append((f['relative'][len('transport/'):-len('.olean')].replace('/','.'),str(path)))
assert len(names)==28506 and len(transports)==1428
pins=json.loads((E/'s6-sdk-selected-cut-import-pins.json').read_text());old=json.loads((E/'sdk-current-incremental-20261024/input-pins-v2.json').read_text());oldmap={row['module']:row for row in old['inputs']};roots=json.loads((E/'s1-sdk-selected-semantic-trace-v2/receipt.json').read_text())['lean_path'].split(':');inputs=[]
for row in pins['modules']:
 p=Path(row['path']);assert sha(p)==row['sha256'];files=[]
 for suffix in ['', '.server','.private']:
  q=Path(str(p)+suffix)
  if q.exists():files.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
 if row['name'] in oldmap:
  hashes=lambda fs:{Path(f['path']).name:f['sha256'] for f in fs}
  assert hashes(files)==hashes(oldmap[row['name']]['files']),row['name']
 inputs.append(dict(module=row['name'],files=files))
w=Path('/private/tmp/s126-sdk-selected-cut-export-20261025-v1');w.mkdir(mode=0o700,exist_ok=False);(w/'transport').mkdir(mode=0o700)
config=dict(schema='focused-extractor-proof-packet-v1',roots=roots,modules=['S1SdkSelectedSemanticTraceV1'],seeds=['AspisS6SdkSelectedSemanticCut.selected_cut','AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts','AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace'],all_declarations=[],baseline_names=sorted(names),dest=str(w/'transport'))
(P/'input.json').write_text(json.dumps(config,separators=(',',':'))+'\n');(w/'input.json').write_bytes((P/'input.json').read_bytes())
(P/'input-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bases=bases,inputs=inputs,all_previous_selected_inputs_unchanged=True,base_transport=transports,scope='Additional untrusted source-selected SDK cut/S1 consumer logical terms. Reuse all 1428 immutable base fragments. No kernel reconstruction, native binding, security or artifact closure.'),separators=(',',':'))+'\n')
print(json.dumps(dict(work=str(w),modules=len(inputs),base_constants=len(names),base_fragments=len(transports))))
