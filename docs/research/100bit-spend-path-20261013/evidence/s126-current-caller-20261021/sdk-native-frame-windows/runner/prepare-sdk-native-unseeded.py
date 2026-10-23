#!/usr/bin/env python3
"""Remove the prefix/tag initializer from the complete native caller harness.
All proof bytes are arbitrary inputs; source gate and every prior assertion stay.
No proof claim until the changed native caller is checked.
"""
from pathlib import Path
import sys,json,hashlib
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text()
initializer=' unsafe{core::ptr::copy_nonoverlapping(plan().candidate.as_ptr(),b0.as_mut_ptr(),688);}b0[696]=2;'
assert original.count(initializer)==1
source=original.replace(initializer,' // Arbitrary proof bytes: the unchanged source gate establishes prefix/tag validity.')
assert source[:source.index('fn native_parent_arguments()')]==original[:original.index('fn native_parent_arguments()')]
assert source.count('kani::assume(')==original.count('kani::assume(')
assert source.count('assert')==original.count('assert')
(out/'src/lib.rs').write_text(source);(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),base_source_sha256=sha(original),unchanged_source_and_helpers_sha256=sha(source[:source.index('fn native_parent_arguments()')]),qualification=__doc__,domain='Every58295-byte proof input, independent of the arbitrary688-byte encoder reply and arbitrary tag696. All typed statements, metadata, signed SDK borrow flags, nonzero usize Rc fields and checkpoint bytes remain arbitrary as in the predecessor. Native source guard rejects or admits; no prefix/tag initialization or assumption remains.',retained='Common-successful-child hooks, fixed public/checkpoint lengths, canonical data-slot construction/lamport alias mapping, named pure scan overapproximation, heap/runtime embedding, actual child identities and ordered oracle/state/log transport. This is not full S2 closure.'),indent=2)+'\n')
