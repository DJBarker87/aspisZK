from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NJG_src';n='crates/aspis-core/src/lib.rs';p=S/n;old=p.read_text();new='#![cfg_attr(kani, feature(allocator_api))]\n'+old;p.write_text(new)
pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NJG_FEATURE_FIX.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));print('NJG cfg(kani) allocator_api feature enabled')
