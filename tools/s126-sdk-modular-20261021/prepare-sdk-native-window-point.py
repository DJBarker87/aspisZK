#!/usr/bin/env python3
"""Aligned ghost index windows over the unchanged original proof allocation.
Every native byte/metadata/alias input remains arbitrary. Only the observer's
index is partitioned. All 15 windows (and the other roots/safety gates) must
compose before claiming the complete native decoder-prefix byte frame.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);window=int(sys.argv[2]);assert 0<=window<15
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-root-point.py'),str(out),'0'],check=True)
p=out/'src/lib.rs';s=p.read_text();needle='let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());'
assert s.count(needle)==1
s=s.replace(needle,'let offset:u16=kani::any();let selected_index:usize='+str(window*4096)+'+(offset%4096) as usize;kani::assume(selected_index<buffers[selected_root].len());')
p.write_text(s)
p=out/'Cargo.toml';p.write_text(p.read_text().replace('name="aspis-s126-sdk-shared-prefix-root0"','name="aspis-s126-sdk-shared-prefix-root0-window'+str(window)+'"'))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),observer_window=window,window_start=window*4096,window_width=4096,qualification=__doc__,remaining='Original SDK, no method stubs. Need every window with all enabled properties/covers and Lean index coverage, other root cases, native/reference prefix composition, scan/child/runtime/ordered-oracle transport. Decoder-error prefix only; no S2/success-stage closure.')
p.write_text(json.dumps(m,indent=2)+'\n')
