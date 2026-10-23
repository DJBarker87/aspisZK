#!/usr/bin/env python3
"""Check the same full typed cleanup frame by executing every destructor body.
The prior counter-only target still timed out with nested verified contracts.
Here all leaf verified-stub/contract wrappers are removed; the parent alone is
DFCC-enforced. Real standard guard/Box/Vec destructors execute. The ONLY stub is
std dealloc -> actual frozen SDK BumpAllocator::dealloc body, explicitly qualified.
No SDK/guard/model carrier or input bytes are changed or narrowed.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-ordered-cleanup-stack-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();old=s
def block_end(s,start):
 b=s.index('{',start)+1;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return b
for mode in ['shared','exclusive']:
 a=s.index(f'#[cfg(kani)] mod guard_{mode}_certificate');s=s[:a]+s[block_end(s,a):]
a=s.index('#[kani::proof_for_contract(destroy_owner)]');b=block_end(s,s.index('fn actual_owner_step_frame()',a));s=s[:a]+s[b:]
for mode in ['shared','exclusive']:
 f=s.index(f'fn finish_guard_{mode}(');a=s.rfind('#[cfg(kani)]',0,f);s=s[:a]+s[f:]
s=s.replace('#[kani::modifies()]\nfn destroy_owner','fn destroy_owner')
for name in ['destroy_owner','finish_guard_shared','finish_guard_exclusive']:
 s=s.replace(f'#[kani::stub_verified({name})]\n','')
assert '#[kani::stub_verified' not in s
# Exact destructor operation bodies and enclosing order have not changed.
for name in ['finish_guard_shared','finish_guard_exclusive','destroy_owner','ordered_cleanup']:
 a=old.index('fn '+name+'(');b=block_end(old,a);assert old[a:b] in s,name
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-cleanup-stack-frame-v1','ordered-cleanup-direct-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then one parent counter-only DFCC frame with actual destructor bodies, no nested verified contracts, no large copy, complete arbitrary SDK payloads.8G cap unchanged.',remaining='Every assertion/cover must pass. Release dealloc dispatch/valid owner/runtime/ABI and source compiler-cleanup/explicit typed-drop transport remain. Then compose concrete copy and cleanup footprints with caller separation and actual first/child/oracle/TX2 binding. No whole S2.'),indent=2)+'\n')
