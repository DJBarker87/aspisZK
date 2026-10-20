#!/usr/bin/env python3
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
gen=root/'source-snapshot/generated/Funs.lean'
raw=gen.read_text()
opts='set_option maxHeartbeats 1000000\n\n/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n\n'
assert raw.count(opts)==1
clean=(root/'sources/AspisR1WideToBytesIndexedCandidate/FunsNoResourceOptions.lean').read_text()
assert clean==raw.replace(opts,'')
print('PASS exact generated Funs body after removing only maxHeartbeats/maxRecDepth resource options')
print('generated_sha256='+hashlib.sha256(raw.encode()).hexdigest())
print('adapter_sha256='+hashlib.sha256(clean.encode()).hexdigest())
