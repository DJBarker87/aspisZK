#!/usr/bin/env python3
"""Separate first-entry relational control from the enclosing native frame.
Ordinary paired proof assumes no native frame. Original SDK methods execute in
native mode; models mode is separately qualified by direct operation coupling.
Independent same-source byte/effect frames must still compose before identifying
the reused model buffers with initial native inputs.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'native'
assert mode in ['native','models']
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-first-coupled-cmp.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text()
a=s.index('#[kani::modifies(');b=s.index('fn native_prefix(',a);s=s[:a]+s[b:]
s=s.replace('#[kani::proof_for_contract(native_prefix)]','#[kani::proof]')
if mode=='native':
 lines=s.splitlines(keepends=True)
 s=''.join(line for line in lines if not line.startswith('#[kani::stub(AccountInfo::'))
 assert '#[kani::stub(AccountInfo::' not in s
p.write_text(s)
version='v3' if mode=='native' else 'v4'
p=out/'Cargo.toml';p.write_text(p.read_text().replace('first-coupling-v2','first-coupling-'+version))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,sdk_mode=mode,native_frame_assumed=False,native_frame_enforced=False,remaining='All enabled pair properties/covers must pass; no source frame follows from this ordinary paired query. Original native/source frame, relational comparison/scan cut, child instance and successful first-output/writeback transport remain explicit. '+('Original unchanged SDK methods execute, no SDK method/model stub.' if mode=='native' else 'Actual-carrier SDK model contextual transport must consume the direct paired checks and exact native/model acquire+Drop frames.'))
p.write_text(json.dumps(m,indent=2)+'\n')
