#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
b=p/'evidence/pair-zero-scanner-sdk-extraction-v5-stock-20261023'
x=json.loads((b/'input/source-pins.json').read_text())
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for c in x['cuts']:
 s=p/'rust-source'/(c['name']+'-r1_pool_adapter_owned.rs')
 assert sha(s)==c['source_sha256']
 raw=s.read_bytes()[c['start_byte']:c['end_byte_exclusive']]
 assert hashlib.sha256(raw).hexdigest()==c['body_sha256']
 assert raw+b'\n'==(b/'input/fragments'/(c['name']+'.rs')).read_bytes()
 assert raw.decode() in (b/'input/lib.rs').read_text()
for rel,h in x['kit_files'].items():assert sha(b/'input'/rel)==h
for c in json.loads((b/'sdk-nominal-reexports.json').read_text()):
 assert sha(p/'sdk-source'/c['relative_path'])==c['sha256']
a=p/'evidence/pair-zero-scanner-sdk-lean-v1-20261023'
for name,d in json.loads((a/'generated-option-adapter.json').read_text()).items():
 src=(b/'generated/AspisR1ZeroScannerSdkV1'/(name+'.lean')).read_text()
 assert hashlib.sha256(src.encode()).hexdigest()==d['input_sha256']
 out=''.join(s for s in src.splitlines(keepends=True) if not s.startswith('set_option '))+d['audit_suffix']
 assert out==(a/'sources/AspisR1ZeroScannerSdkV1'/(name+'.lean')).read_text()
 assert hashlib.sha256(out.encode()).hexdigest()==d['output_sha256']
print('Exact current/H5 Rust spans, real SDK nominal sources, kit hashes and reversible generated-option adapter checked.')
