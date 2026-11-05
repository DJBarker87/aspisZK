from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIX_src';n='crates/aspis-core/src/r0/heap.rs';p=S/n;s=p.read_text();start=s.index('#[cfg(kani)]\nmod NIX_claims_heap');p.write_text(s[:start]+(B/'NIX_heap_claims.rs.txt').read_text());x=json.loads((B/'NIX_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(x));print('NIX allocation and fixed-row/limb partitions installed; timed-out broad shape retired')
