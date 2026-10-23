#!/usr/bin/env python3
"""Same-allocation native/full-reference decoder-prefix join, frame separated.
The native byte frame is certified by independent allocation/index cases, not
assumed by this harness or re-instrumented across the second execution. These
checks alone give no initial-buffer preservation or whole-stage equivalence.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-shared-prefix.py'),str(out),'unreachable-cuts','exact-vec','constructor-errors'],check=True)
p=out/'src/lib.rs';s=p.read_text();s=s.replace('#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]','#[kani::proof] #[kani::unwind(48)]')
a=s.index('#[kani::modifies(');b=s.index('fn native_prefix(',a);s=s[:a]+s[b:]
s=s.replace('// Native handles are now gone. The native modifies contract must have proved\n // that no account bytes/Vec descriptor or other external allocation changed.','// Native handles are gone. Independent all-root/window frame certificates\n // are required before identifying these bytes with the initial heap.')
p.write_text(s)
p=out/'Cargo.toml';p.write_text(p.read_text().replace('name="aspis-s126-sdk-shared-prefix"','name="aspis-s126-sdk-shared-prefix-pair-separated-frame"'))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Every all-root/index-window native frame certificate must be linked at identical native source/SDK/harness domain, plus checked index coverage, before initial-heap identification. Native decoder error prefix and model scan=false/reached-native pure scan abstraction only. Actual success continuations, child/runtime/oracle/state joins remain. No native frame assumed by a contract; this is an ordinary proof harness with no SDK method stubs.')
p.write_text(json.dumps(m,indent=2)+'\n')
