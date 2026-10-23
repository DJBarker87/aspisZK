#!/usr/bin/env python3
"""Extend the complete unseeded native caller's byte-frame postconditions.
No callee or caller operation is changed; observe original allocations directly.
"""
from pathlib import Path
import json,sys,hashlib
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text();source=original
marker=' let actual=adapter::run(&program,&accounts,&instruction[..instruction_len]);'
assert source.count(marker)==1
source=source.replace(marker,''' let proof_observed:usize=kani::any();kani::assume(proof_observed<58295);
 let public_observed:usize=kani::any();kani::assume(public_observed<1880);
 let proof_before=unsafe{NATIVE_ROOT_PTRS.value[0].add(proof_observed).read()};
 let public_before=unsafe{NATIVE_ROOT_PTRS.value[1].add(public_observed).read()};
 let checkpoint_before=unsafe{NATIVE_ROOT_PTRS.value[2].add(observed).read()};
'''+marker+'''
 assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[0].add(proof_observed).read()},proof_before,"native caller preserves every proof byte on both returned statuses");
 assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[1].add(public_observed).read()},public_before,"native caller preserves every public byte on both returned statuses");
 if actual.is_err() {assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[2].add(observed).read()},checkpoint_before,"native caller preserves every checkpoint byte on returned error");}
''',1)
checkpoint_only='checkpoint-only' in sys.argv[3:]
if checkpoint_only:
 lines=source.splitlines(keepends=True)
 source=''.join(line for line in lines if not any(word in line for word in ['proof_observed','public_observed','let proof_before=','let public_before=']))
assert source[:source.index('fn native_parent_arguments()')]==original[:original.index('fn native_parent_arguments()')]
assert 'b0[696]=2' not in source
(out/'src/lib.rs').write_text(source);(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),base_source_sha256=sha(original),unchanged_source_and_helpers_sha256=sha(source[:source.index('fn native_parent_arguments()')]),qualification=__doc__,domain='Arbitrary unseeded proof58295/public1880/checkpoint1768 buffers and all native predecessor scalar/account states. Independent symbolic coordinates observe proof/public buffers on every returned status; checkpoint coordinate observes exact encoder output on success and unchanged byte on error. The source stage1, common child hooks and every existing scalar/caller assertion stay unchanged.',retained='Same fixed lengths, common successful child replies, pure scan overapproximation, canonical data/lamport slot model, runtime heap embedding, actual child identities, and ordered state/log/oracle transport. Not a total native-to-owned or whole S2 closure.'),indent=2)+'\n')
if checkpoint_only:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['domain']='All unseeded native predecessor inputs retained. Only the already existing arbitrary checkpoint coordinate is queried additionally before the unchanged native source call; successful calls keep their exact output-byte assertion and returned errors must preserve this original byte. No new large proof/public coordinate query. The whole caller, all original assertions, arbitrary Rc counts, metadata, buffers and rejection branches remain.';p.write_text(json.dumps(m,indent=2)+'\n')
