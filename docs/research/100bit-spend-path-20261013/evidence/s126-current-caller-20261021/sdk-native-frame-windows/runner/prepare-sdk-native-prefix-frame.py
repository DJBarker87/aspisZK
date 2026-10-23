#!/usr/bin/env python3
"""Isolate the native prefix's frame before loading a second execution.

No SDK/model stubs are added. This intentionally proves only the native frame,
with the same arbitrary heap and decoder-error cut, not paired correspondence.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-shared-prefix.py'),str(out),'unreachable-cuts','exact-vec','constructor-errors'],check=True)
p=out/'src/lib.rs';s=p.read_text()
s=s.replace('use aspis_s126_owned_sdk_borrowed as owned;\nuse owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};\n','')
s=s.replace('fn planned_scan(_: &[u8])->bool{false}\n','')
for line in ['#[kani::stub(aspis_s126_owned_sdk_borrowed::first_decoded,unreachable_first)]\n','#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]\n','#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]\n']:
 assert line in s;s=s.replace(line,'')
a=s.index(' // Native handles are now gone.');b=s.index('\n}\n}',a)
s=s[:a]+''' // The concrete native body has returned and all its guard drops ran.
 assert!(actual.is_err());
 kani::cover!(unsafe{HITS.value[0]}==1,"native decoder entry with native-only frame");
 kani::cover!(unsafe{HITS.value[0]}==1&&initial_counts[0]==isize::MAX,"decoder entry before proof acquisition permits saturated proof counter");
'''+s[b:]
p.write_text(s)
p=out/'Cargo.toml';c=p.read_text();lines=[l for l in c.splitlines() if not l.startswith('aspis-s126-owned-sdk-borrowed=')];assert len(lines)+1==len(c.splitlines());p.write_text('\n'.join(lines)+'\n')
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='Same full arbitrary fixed-root buffers/SDK metadata/Rc counters/aliases as shared-prefix harness. Native only; no owned reference loaded or executed. Native source prefix hash is unchanged.',remaining='All native DFCC safety/frame properties must pass. No reference success, shared-heap correspondence or full native stage1 success follows. Decoder-error and pure scan abstraction remain explicit.')
p.write_text(json.dumps(m,indent=2)+'\n')
