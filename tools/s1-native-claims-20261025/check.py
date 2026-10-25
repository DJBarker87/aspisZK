#!/usr/bin/env python3
"""Read-only native-function/model-check evidence scope guard."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-native-claims-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
original=subprocess.check_output(['git','show',freeze+':crates/aspis-r1-cost-probe/src/r1_semantic.rs'],cwd=R,text=True)
a=original.index('#[inline(never)]\nfn claims(');b=original.index('\n#[inline(never)]',a+1)
body=original[a:b]
for name in ['s1-native-claims-v1','s1-native-claims-v2']:
    A=E/name;i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
    assert r['exit_status']==0 and r['watchdog_stop'] is None and r['swaps']==0
    assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
    assert 'uninit-checks' not in r['command']
    assert r['command'][r['command'].index('--harness')+1]=='native_claims::proofs::native_claims_full_trace'
    for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
    for p in (A/'source').rglob('*'):
        if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
    native=(A/'source/min/src/native_claims.rs').read_text()
    assert native=='use crate::r1_wire::{self as wire,Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'+body+'\n#[cfg(kani)]\n#[path="native_claims_proofs.rs"]\nmod proofs;\n'
    wire=(A/'source/min/src/wire_claims.rs').read_text()
    base=(E/'s1-init-local-20261025/original-min/src/r1_wire.rs').read_text()
    assert wire==base+'''\n#[cfg(kani)]
pub(crate) fn s1_claims_probe_prefix<'a>(root:&'a[u8;32],frame:&'a[u8])->Prefix<'a>{Prefix{c1_root:root,records:[frame;27]}}
'''
    proof=(A/'source/min/src/native_claims_proofs.rs').read_text()
    assert proof==(R/'tools/s1-native-claims-20261025/proofs.rs').read_text()
    assert 'kani::assume' not in proof
    assert proof.count('#[kani::stub(')==1
    assert '#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]' in proof
    for required in ['assert!(offset==p*29)','assert!(record.row()==25)',
        'assert!(record.framed().as_ptr()==FRAME_PTR)', 'assert!(record.framed().len()==FRAME_LEN)',
        'if calls==0{assert!(actual==Error::Allocation);}',
        'assert!(calls==fail_at+1)','assert!(actual==error)','assert!(calls==3)']:
        assert required in proof,required
    if name.endswith('v2'):
        log=(A/'stdout.log').read_text()
        assert '0 of 747 failed' in log and '3 of 3 cover properties satisfied' in log
        assert 'VERIFICATION:- SUCCESSFUL' in log and r['verification_launched']
    else:assert not r['verification_launched']
print(f'PASS {len(m["files"])} source/evidence hashes; complete frozen Claims return/decoder trace checked; initialization/SDK/native installation OPEN')
