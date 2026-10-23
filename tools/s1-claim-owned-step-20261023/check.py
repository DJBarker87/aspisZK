#!/usr/bin/env python3
"""Audit pinned source coupling without rerunning unchanged Kani work."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-claim-owned-reference/native-source-step-strict'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(P/'manifest.json')
assert set(m['files'])=={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}-{'manifest.json'}
for rel,d in m['files'].items():assert sha(P/rel)==d,rel
assert not any(p.suffix in ['.olean','.out','.exe','.o','.rlib','.pyc','.llbc'] for p in P.rglob('*'))
A=P/'attempt';r=load(A/'receipt.json');i=load(A/'input.json')
assert r['exit_status']==0 and r['swaps']==0
assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
assert '-C opt-level=3' in i['env']['RUSTFLAGS'] and '-Z mir-opt-level=0' in i['env']['RUSTFLAGS']
log=(A/'stdout.log').read_text();assert '0 of 828 failed' in log and '3 of 3 cover properties satisfied' in log
for rel,d in i['crate_source_pins'].items():assert sha(P/'input'/rel)==d,rel
assert sha(P/'input/Cargo.lock')==i['cargo_lock_sha256']
before=load(A/'all-local-before.json')['dependencies'];after=load(A/'all-local-after.json')['unchanged']
assert before.keys()==after.keys() and all(after.values()) and len(before)==7
for name,row in before.items():
 if row['root'].endswith('aspis-s1-claim-owned-step-v6'):
  for rel,d in row['files'].items():assert sha(P/'input'/rel)==d,rel
 if row['root'].endswith('frozen-probe'):
  for rel,d in row['files'].items():assert sha(P/'input/frozen-probe'/rel)==d,rel
freeze=load(E/'s1-claim-owned-reference/native-dependency-freeze-comparison.json')
assert all(not row['differences'] for row in freeze['dependencies'])
assert freeze['revision']=='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
for name,row in before.items():
 if row['root'].endswith('/frozen-source/crates/aspis-statement'):
  for rel,d in row['files'].items():assert sha(P/'input/frozen-source/crates/aspis-statement'/rel)==d,rel
features=load(P/'feature-query/features.json')
assert features['lock_unchanged'] and features['lock_sha256']==i['cargo_lock_sha256']
b=load(P/'input/owned-step-binding.json')
owned=E/'s1-claim-uf/inputs/s1-claim-owned-nested-v7/input/lib.rs'
assert sha(owned)==b['owned_source_sha256']
assert b['owned_fragment'] in (P/'input/src/lib.rs').read_text()
proof=(P/'input/src/proofs.rs').read_text()
for text in ['kani::assume(point<6&&l<29)','assert_eq!(old,new)','assert_eq!(state,PUSH_INPUT)',
             'assert_eq!(frame,FIELD_INPUT)','assert_eq!(a,if error{Err(Error::Parse)}else{Ok(())})']:
 assert text in proof,text
print(json.dumps(dict(native_source_step_checks=828,covers=3,all_local_path_dependencies=7,
 actual_complete_carriers=True,whole_original_claim_equivalence=False,whole_s1_closed=False,whole_s6_closed=False)))
