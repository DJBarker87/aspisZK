from pathlib import Path
import json,hashlib,lzma,shutil
B=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
export=json.loads((B/'NKA_EXPORT.json').read_text())
for r in export['files']:assert sha(Path(r['path']))==r['sha256'],r['path']
raw=lzma.decompress((B/'NKA_RESOLVED_OBJECTS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NKA_RESOLVED_OBJECTS.json.sha256').read_text().strip()
resolved=json.loads(raw)['selected'];paths=json.loads((B/'NKA_CONSUMER_PATHS.json').read_text())+['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
for r in resolved:
 assert sha(Path(r['path']))==r['sha256'],r['path']
 leaf=r['module'].split('.')[-1];name=Path(r['path']).name;assert name.startswith(leaf)
 rel=r['module'].replace('.','/')+name[len(leaf):]
 selected=next((Path(root)/rel for root in paths if (Path(root)/rel).is_file()),None);assert selected is not None,rel
 assert sha(selected)==r['sha256'],rel
mods=json.loads((B/'NKA_MODULES.json').read_text());sources=[]
for m in mods:
 candidates=[B/'NKA_generated'/(m['module']+'.lean')]
 p=next((p for p in candidates if p.is_file()),None);assert p is not None,m
 assert sha(p)==m['sha256'],str(p);sources.append(dict(module=m['module'],source=str(p),sha256=m['sha256']))
S=B/'NKA_src';assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for n,h in {**json.loads((B/'NKA_FROZEN_FILE_PINS.json').read_text()),**json.loads((B/'NKA_SOURCE_PINS.json').read_text())}.items():assert sha(S/n)==h,n
archives=[]
for p in sorted((B/'NKA_archives_final').glob('*.xz')):
 raw=lzma.decompress(p.read_bytes());h=hashlib.sha256(raw).hexdigest();assert h==p.with_suffix('.sha256').read_text().strip()
 archives.append(dict(path=str(p.relative_to(B)),bytes=p.stat().st_size,sha256=sha(p),uncompressed_bytes=len(raw),uncompressed_sha256=h))
report=dict(status='PASS',export_bytes=export['total_bytes'],export_modules=export['modules'],selected_objects_checked=len(resolved),consumer_objects_byte_identical=True,consumer_check='Full selected object+private/server/IR hash equivalence; no third combined compile',sources=sources,archives=archives,lock_unchanged=True,cargo_target_dir=str(B/'NKA_target'),free_bytes=shutil.disk_usage(B).free)
(B/'NKA_FINAL_HOST_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print('NJT retained objects, full consumer resolution, source pins, archives and lock PASS')
