#!/usr/bin/env python3
"""Append test items inside an existing cfg(test) module in a disposable host copy.
No production tokens change. Refuses a second injection or a source hash mismatch.
"""
from pathlib import Path
import hashlib,json,sys
root=Path(sys.argv[1]); snippet=Path(sys.argv[2]); pins=json.loads(Path(sys.argv[3]).read_text())
p='programs/aspis-pool/src/pair_forest.rs'; src=root/p
raw=src.read_bytes(); assert hashlib.sha256(raw).hexdigest()==pins[p]
assert raw.rstrip().endswith(b'}') and b'#[cfg(test)]\nmod tests {' in raw
cut=raw.rfind(b'}'); addition=snippet.read_bytes()
assert b'r20_hint_reorder' not in raw
src.write_bytes(raw[:cut]+addition+b'\n'+raw[cut:])
(root.parent/'test-injection.json').write_text(json.dumps(dict(source=p,original_sha256=pins[p],snippet_sha256=hashlib.sha256(addition).hexdigest(),instrumented_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),production_prefix_unchanged=True,method='Insert only new test items immediately before final cfg(test) module brace'),indent=2)+'\n')
