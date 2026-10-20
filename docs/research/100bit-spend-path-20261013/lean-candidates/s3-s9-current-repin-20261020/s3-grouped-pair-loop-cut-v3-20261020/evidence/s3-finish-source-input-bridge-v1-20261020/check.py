#!/usr/bin/env python3
"""Read-only integrity checker for the S3 finish-source-input proof packet."""
from pathlib import Path
import hashlib, json, sys
p=Path(__file__).resolve().parent
repo=next((q for q in p.parents if (q/'AGENTS.md').is_file() and (q/'docs/research/100bit-spend-path-20261013').is_dir()),None)
if repo is None: raise SystemExit('repository root not found')
errors=[]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
checks=json.loads((p/'files.sha256.json').read_text())
for rel,want in checks.items():
    f=p/rel
    if not f.is_file(): errors.append(f'missing packet file {rel}'); continue
    if sha(f)!=want: errors.append(f'packet hash mismatch {rel}')
for x in p.rglob('*'):
    if x.is_file() and x.suffix in {'.olean','.ilean','.ir','.llbc','.exe'}: errors.append(f'forbidden compiled artifact {x.relative_to(p)}')
mi=json.loads((p/m['direct_import_source_map']).read_text())
if mi.get('schema')!='focused-extractor-proof-packet-v1-source-import-map': errors.append('bad import-map schema')
mods={x['module']:x for x in m['modules']}
expected={}
for mod in m['modules']:
    src=p/mod['source']
    if not src.is_file() or sha(src)!=mod['source_sha256']: errors.append(f"compiled source pin mismatch {mod['module']}")
    receipt=(p/mod.get('receipt',mod['evidence']+'/receipt.json'))
    if not receipt.is_file(): errors.append(f"missing receipt {mod['module']}")
    else:
        r=json.loads(receipt.read_text())
        if r.get('exit_status')!=0: errors.append(f"non-green receipt {mod['module']}")
        if r.get('source_sha256')!=mod['source_sha256']: errors.append(f"receipt source mismatch {mod['module']}")
        if r.get('object_sha256')!=mod['object_sha256']: errors.append(f"receipt object mismatch {mod['module']}")
    rows=[]
    for dep in mod.get('direct_imports',[]):
        if dep['module'] in mods:
            dsrc=p/mods[dep['module']]['source']
        else:
            dsrc=repo/dep['source']
        if not dsrc.is_file() or sha(dsrc)!=dep['source_sha256']:
            errors.append(f"direct source pin mismatch {mod['module']} <- {dep['module']}")
        rows.append({k:dep[k] for k in ('module','source','source_sha256','object_sha256')})
    expected[mod['module']]=rows
if mi.get('direct_imports_by_target')!=expected: errors.append('direct import source map differs from manifest')
if len(m['modules'])!=6: errors.append('expected exactly six checked modules')
if errors:
    print('FAIL'); print('\n'.join(errors)); sys.exit(1)
print('PASS: packet file hashes, six checked source/receipt pins, direct-import source map, and no-binary policy')
