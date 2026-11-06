from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;n='programs/r1-cost-probe/src/lib.rs';p=B/'NJG_src'/n;old=p.read_text();new=old+'\n#[cfg(kani)] extern crate alloc;\n';p.write_text(new)
x=json.loads((B/'NJG_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(x));(B/'NJG_PROGRAM_ALLOC.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));print('NJG cfg(kani) alloc import repaired')
