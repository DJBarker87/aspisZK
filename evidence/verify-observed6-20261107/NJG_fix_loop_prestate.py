from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=B/'NJG_src'/n;old=p.read_text();start=old.index('#[cfg(kani)] pub mod NJG_claims_loop');end=old.index('#[cfg(kani)] pub mod NJG_rounds_driver',start);new=old[:start]+(B/'NJG_claims_loop.rs.txt').read_text()+'\n'+old[end:];p.write_text(new)
x=json.loads((B/'NJG_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(x));(B/'NJG_LOOP_PRESTATE_FIX.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));print('NJG current row remains uninitialized; only prior-prefix observation is initialized')
