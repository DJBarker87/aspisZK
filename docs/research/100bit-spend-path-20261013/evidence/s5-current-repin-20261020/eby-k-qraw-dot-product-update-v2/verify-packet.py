#!/usr/bin/env python3
import hashlib,json,pathlib,sys
p=pathlib.Path(__file__).resolve().parent
repo=next((q for q in p.parents if (q/'AGENTS.md').is_file() and (q/'docs/research/100bit-spend-path-20261013').is_dir()),None)
if repo is None: raise SystemExit('repository root not found')
m=json.loads((p/'manifest.json').read_text())
errors=[]
for item in m['files']:
    f=p/item['path']
    if not f.is_file(): errors.append(f"missing {item['path']}"); continue
    raw=f.read_bytes()
    if len(raw)!=item['bytes']: errors.append(f"size mismatch {item['path']}")
    if hashlib.sha256(raw).hexdigest()!=item['sha256']: errors.append(f"hash mismatch {item['path']}")
for x in p.rglob('*'):
    if x.is_file() and x.suffix in {'.olean','.ilean','.ir','.llbc'}: errors.append(f"forbidden artifact {x.relative_to(p)}")
source=p/'sources/EbyKPushDecodedProductUpdateV1.lean'
s=source.read_text()
for bad in ['sorry','admit','axiom ','set_option maxHeartbeats','set_option maxRecDepth']:
    if bad in s: errors.append(f"forbidden source token {bad}")
if 'successful_push_decoded_product_update' not in s: errors.append('target theorem missing')
log=(p/'evidence/lean.log').read_text()
if 'successful_push_decoded_product_update' not in log or 'propext' not in log or 'Quot.sound' not in log: errors.append('axiom audit evidence missing')
pre=json.loads((p/'evidence/preflight.json').read_text())
receipt=json.loads((p/'evidence/receipt.json').read_text())
if receipt.get('exit_status')!=0: errors.append('receipt is not exit 0')
# Find source and object pin rows in preflight recursively.
def walk(x):
    if isinstance(x,dict):
        yield x
        for v in x.values(): yield from walk(v)
    elif isinstance(x,list):
        for v in x: yield from walk(v)
rows=list(walk(pre))
for key,entry in json.loads((p/'direct_import_source_map.json').read_text())['direct_imports'].items():
    if key in ('Lean4.32.0','Aeneas Std'): continue
    src=p/entry['source']
    if not src.exists() or hashlib.sha256(src.read_bytes()).hexdigest()!=entry['source_sha256']:
        errors.append(f"direct source pin mismatch {key}")
    # preflight should contain the object hash.
    if not any(entry['object_sha256'] in json.dumps(row,sort_keys=True) for row in rows): errors.append(f"preflight object pin missing {key}")
    uprel=pathlib.Path(entry['upstream_packet'])
    upstream=(p/uprel/'manifest.json') if uprel.parts[0]=='upstream' else (repo/'docs/research/100bit-spend-path-20261013'/uprel/'manifest.json')
    if not upstream.exists() or hashlib.sha256(upstream.read_bytes()).hexdigest()!=entry.get('upstream_manifest_sha256'):
        errors.append(f"upstream packet pin mismatch {key}")
if errors:
    print('FAIL')
    print('\n'.join(errors)); sys.exit(1)
print('PASS: packet files, source/object pins, upstream manifests, Lean receipt, axiom audit, and no-binary policy')
