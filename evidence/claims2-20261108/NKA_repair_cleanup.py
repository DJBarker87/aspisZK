from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NKA_src';n='crates/aspis-core/src/r0/heap.rs';p=S/n;pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
old=p.read_text();a=old.index('#[cfg(kani)] mod NKA_heap_effects');p.write_text(old[:a]+(B/'NKA_heap_effects.rs.txt').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKA_CLEANUP_REPAIR.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
print('NKA cleanup control repaired at original name: duplicate deallocation replaces undetected leak')
