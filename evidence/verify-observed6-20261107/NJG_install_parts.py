from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;n='crates/aspis-core/src/r0/heap.rs';p=B/'NJG_src'/n;old=p.read_text();new=old+'\n'+(B/'NJG_row_parts.rs.txt').read_text();p.write_text(new)
x=json.loads((B/'NJG_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(x));(B/'NJG_PARTS_INSTALL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));print('NJG allocator-free single-limb row-store split installed')
