#!/usr/bin/env python3
"""Read-only failure/origin audit. A passing audit is NOT a proof result."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-claims-init-allocation-cut-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
assert m['accepted_proofs']==[]
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
s=subprocess.check_output(['git','show',freeze+':crates/aspis-r1-cost-probe/src/r1_semantic.rs'],cwd=R,text=True)
a=s.index('#[inline(never)]\nfn claims(');b=s.index('\n#[inline(never)]',a+1);body=s[a:b]
expected='use crate::r1_wire::{self as wire,Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'+body+'\n#[cfg(kani)]\n#[path="native_claims_proofs.rs"]\nmod proofs;\n'
base=E/'s1-native-claims-v2/source/min/src/wire_claims.rs'
for n in range(1,7):
    A=E/f's1-claims-init-allocation-cut-v{n}'
    i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
    assert r['exit_status']==(0 if n%2 else 1)
    assert r['verification_launched']==(n%2==0)
    assert r['swaps']==0 and r['watchdog_stop'] is None
    assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
    assert 'uninit-checks' in r['command'] and '--unwinding-assertions' in r['command']
    assert r['command'][r['command'].index('--harness')+1]=='native_claims::proofs::native_claims_init_allocation_cut'
    assert i['guard']==dict(aggregate_rss_limit_bytes=2*2**30,wall_limit_seconds=180,process_limit=64,one_job=True,local_shared_lock=True)
    for f,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/f)==r[key]
    for p in (A/'source').rglob('*'):
        if p.is_file() and p.name!='run.py':
            rel=str(p.relative_to(A/'source'))
            if rel=='min/src/probe_prepared.rs':
                # Historical runner snapshotted this UNUSED old root instead
                # of the new selected root. Its bytes are not an execution pin.
                assert p.read_bytes()==(E/'s1-native-prepared-v6/source/min/src/probe_prepared.rs').read_bytes()
            else:assert sha(p)==i['source_files'][rel]
    # Selected root has contemporaneous input/pre/post hashes, reconstructed
    # here from the maintained source; NOT a retrospective snapshot claim.
    assert sha(R/'tools/s1-claims-init-allocation-cut-20261025/probe.rs')==i['source_files']['min/src/probe_claims_init_cut.rs']
    D=A/'source/min/src/claims_init_cut'
    assert (D/'native_claims.rs').read_text()==expected
    assert (D/'wire_claims.rs').read_bytes()==base.read_bytes()
    proof=(D/'native_claims_proofs.rs').read_text()
    assert 'kani::assume' not in proof and 'transmute' not in proof
    assert proof.count('#[kani::stub(')==2
    assert '#[kani::stub(aspis_core::r0::heap::uninit,fresh_uninitialized)]' in proof
    assert 'alloc::alloc::alloc(layout)' in proof
    assert 'Box::from_raw(ptr.cast::<core::mem::MaybeUninit<T>>())' in proof
    if n>=5:assert proof==(R/'tools/s1-claims-init-allocation-cut-20261025/proofs.rs').read_text()
    log=(A/'stdout.log').read_text()
    if n in [2,4]:
        assert 'Cannot determine layout for an Enum of type r1_wire::Error, as it has multiple variants that have different padding.' in log
        assert f'1 of {606 if n==2 else 602} failed' in log
    if n==6:
        assert '1 of 469 failed' in log and '0 of 1 cover properties satisfied' in log
        assert 'Interaction between raw pointers and unions is not yet supported.' in log
        assert 'File: "src/claims_init_cut/native_claims.rs", line 11' in log
    if n%2==0:assert 'VERIFICATION:- FAILED' in log
print(f'PASS {len(m["files"])} failure/source hashes; 3 compile successes, 3 excluded verification failures; NO initialization/whole-S1 closure.')
