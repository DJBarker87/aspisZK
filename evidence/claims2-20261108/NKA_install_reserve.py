from pathlib import Path
import hashlib,json,difflib
B=Path(__file__).resolve().parent;S=B/'NKA_src';n='crates/aspis-core/src/r0/heap.rs';p=S/n
frozen=json.loads((B/'NKA_FROZEN_FILE_PINS.json').read_text());pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
old=p.read_text();body=(B/'NKA_ReserveContinuation.rs.txt').read_text();p.write_text(old+'\n'+body)
pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKA_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
(B/'NKA_RESERVE_CONTINUATION.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
# Check that the continuation is literal shipped text up to harmless wrapping.
start=old.index('    unsafe {');end=old.rfind('}')
fragment=old[start:end];assert 'out.set_len(1)' in fragment and 'Box::into_raw(out.into_boxed_slice())' in fragment and 'Box::from_raw(ptr)' in fragment
(B/'NKA_RESERVE_SITE.json').write_text(json.dumps(dict(source=n,frozen_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(body.encode()).hexdigest(),request_bytes=1392,request_align=4,source_call='out.try_reserve_exact(1)',scope='unsafe allocation continuation only; no data/allocator outcome claim',cargo_target_dir=str(B/'NKA_target')),indent=2))
print('NKA allocation-only continuation installed')
