#!/usr/bin/env python3
"""Split the ghost observation by allocation, retaining every native input.
The root is a proof observer only, never an argument of the original caller.
All three root cases and safety/ABI/runtime composition are required before a
whole native byte-frame claim; a single case is not that claim.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);root=int(sys.argv[2]);assert 0<=root<3
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-point-frame.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text();old='let selected_root:usize=kani::any();kani::assume(selected_root<3);'
assert s.count(old)==1;s=s.replace(old,'let selected_root:usize='+str(root)+';')
p.write_text(s)
p=out/'Cargo.toml';c=p.read_text().replace('name="aspis-s126-sdk-shared-prefix"','name="aspis-s126-sdk-shared-prefix-root'+str(root)+'"');p.write_text(c)
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),observer_root=root,qualification=__doc__,remaining='Same original actual SDK and native code, no method stubs; decoder-error and pure-scan cut remain. Every arbitrary byte index in this one root is observed, every original buffer byte remains unconstrained. Need all three roots plus complete safety/caller/runtime/scan composition before whole byte-frame or S2 closure.')
p.write_text(json.dumps(m,indent=2)+'\n')
