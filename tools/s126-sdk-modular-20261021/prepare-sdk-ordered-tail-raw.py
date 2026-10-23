#!/usr/bin/env python3
"""Ordered full SDK tail link with typed raw guard destruction cuts.
Avoids by-value verified guard-stub cleanup: the failed predecessor trace
contains an additional actual Drop after the stub postcondition. Every new
raw guard contract is checked independently; no SDK model or opaque carrier.
This is still an explicit-cleanup candidate with source/runtime equivalence
and allocator/owner/ABI obligations, not adoption or whole S2.
"""
from pathlib import Path
import subprocess,json,hashlib,sys,tempfile
R=Path(__file__).resolve().parents[2];T=R/'tools/s126-sdk-modular-20261021';O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(T/'prepare-sdk-ordered-tail-links.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
for mode in ['shared','exclusive']:
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'leaf';subprocess.run(['python3',str(T/'prepare-sdk-raw-drop-frame.py'),str(out),mode],check=True)
  leaf=(out/'src/lib.rs').read_text();a=leaf.index('#[cfg(kani)]\n#[kani::requires(');b=leaf.index('#[cfg(kani)] mod proofs',a)
  raw=leaf[a:b].replace('finish_guard',f'finish_guard_{mode}')
  a=s.index('#[cfg(kani)]\n#[kani::requires(',s.index('fn statement()->'))
  # Select the named old guard wrapper, not another helper's contract.
  end=s.index(f'fn finish_guard_{mode}(',a);a=s.rfind('#[cfg(kani)]',a,end);b=s.index('\n\n',end)+2
  s=s[:a]+raw+s[b:]
  raw_harness=leaf[leaf.index('#[cfg(kani)] mod proofs'):].replace('mod proofs {',f'mod guard_{mode}_certificate {{',1).replace('finish_guard',f'finish_guard_{mode}')
  a=s.index(f'#[cfg(kani)] mod guard_{mode}_certificate');b=s.index('{',a)+1;depth=1
  while depth:
   depth+=(s[b]=='{')-(s[b]=='}');b+=1
  s=s[:a]+raw_harness+s[b:]
needle=' let mut statement=std::mem::ManuallyDrop::new(statement);';assert s.count(needle)==1
s=s.replace(needle,''' let mut proof=std::mem::ManuallyDrop::new(proof);
 let mut public=std::mem::ManuallyDrop::new(public);
 let mut checkpoint=std::mem::ManuallyDrop::new(checkpoint);
'''+needle)
s=s.replace('encoded_finish(&mut checkpoint,&bytes,','encoded_finish(&mut *checkpoint,&bytes,')
s=s.replace('finish_guard_shared(proof,counters[0]);','finish_guard_shared(&mut *proof,counters[0]);').replace('finish_guard_shared(public,counters[1]);','finish_guard_shared(&mut *public,counters[1]);').replace('finish_guard_exclusive(checkpoint,counters[2]);','finish_guard_exclusive(&mut *checkpoint,counters[2]);')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-tail-links-v1','ordered-tail-links-raw-v2'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Verify both raw guard leaf harnesses before the ordered-link caller. Then all assertions and covers, exact source cleanup/candidate equivalence and frame union, frozen allocator/valid owners/runtime/ABI, and actual first/child/oracle/TX2 transport remain. No enclosing frame assumed; no whole S2.'),indent=2)+'\n')
