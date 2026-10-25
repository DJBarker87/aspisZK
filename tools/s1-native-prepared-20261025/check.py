#!/usr/bin/env python3
"""Read-only checks of frozen constructor origins and bounded Kani receipts."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-native-prepared-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
b=json.loads((P/'source-kit-binding.json').read_text())
assert b['freeze']=='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
for key,row in b['selected_spans'].items():
    original=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-r1-cost-probe/src/'+row['file']],cwd=R).decode()
    assert hashlib.sha256(original.encode()).hexdigest()==row['whole_source_sha256']
    value=original[row['offset']:row['offset']+row['length']]
    assert value==b['selected'][key] and hashlib.sha256(value.encode()).hexdigest()==row['sha256']
for n in range(1,7):
    A=E/f's1-native-prepared-v{n}'
    i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
    assert r['exit_status']==(1 if n==4 else 0)
    assert r['swaps']==0 and r['watchdog_stop'] is None
    assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
    assert r['verification_launched']==(n in [2,4,6])
    assert 'uninit-checks' not in r['command'] and '--unwinding-assertions' in r['command']
    assert i['guard']['aggregate_rss_limit_bytes']==2*2**30 and i['guard']['wall_limit_seconds']==180
    for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
    for p in (A/'source').rglob('*'):
        if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
    native=(A/'source/min/src/prepared_native/verifier.rs').read_text()
    for key in ['Error','View','Prepared','prepared_claim','Prepared_impl']:assert b['selected'][key] in native
    for rel,h in b['payload_files'].items():assert sha(A/'source/min/src/prepared_native'/rel)==h
    proof=(A/'source/min/src/prepared_native/proofs.rs').read_text()
    assert 'kani::assume' not in proof and 'transmute' not in proof
    assert '#[kani::unwind(257)]' in proof
    # Snapshots v1/v2 predate the negative control, and v1-v4 predate the
    # all-semantic-fields broadening. Never relabel them as the current proof.
    if n>=5:
        assert proof==(R/'tools/s1-native-prepared-20261025/proofs.rs').read_text()
        assert proof.count('#[kani::stub(')==12
        assert 'claims:Box::new([any_row(),any_row(),any_row()])' in proof
        assert 'final_message=kani::any::<[u8;2048]>()' in proof
        for needed in ['assert!(g as *const [E;29]==G_PTR)', 'same_powers(g,&POWERS)',
          'assert!(sem as *const Verified<H> as *const ()==SEM_PTR)', 'same_e(kappa,SCALARS[1])',
          'G_PTR=&scratch', 'G_PTR=&initial', 'assert!(row==31)', 'assert!(row==32)',
          'same_bytes(&out.state,&states[6])', 'same_q(out.semantic_alpha[i],alpha[i])']:
            assert needed in proof,needed
    log=(A/'stdout.log').read_text()
    if n in [2,6]:
        assert f'0 of {1582 if n==6 else 1576} failed' in log
        assert '3 of 3 cover properties satisfied' in log and 'VERIFICATION:- SUCCESSFUL' in log
    if n==4:
        assert '1 of 1576 failed' in log and 'VERIFICATION:- FAILED' in log
        assert 'Failed Checks: assertion failed: g as *const [E; 29] == G_PTR' in log
# Kit is a source reconstruction, not a compiler execution. At the final
# positive snapshot every emitted source file which was snapshotted is exact.
final=E/'s1-native-prepared-v6/source'
for p in final.rglob('*'):
    if p.is_file() and p.name!='run.py':
        rel=str(p.relative_to(final));assert sha(p)==b['files'][rel],rel
# Original core + sampler are pre/post pinned even though not duplicated in
# each run snapshot. Their source-only regeneration is available from Git.
i=json.loads((E/'s1-native-prepared-v6/input.json').read_text())
for rel,h in b['files'].items():
    assert i['source_files'][rel]==h,rel
    if rel.startswith('core-workspace/crates/'):
        data=subprocess.check_output(['git','show',b['freeze']+':'+rel.removeprefix('core-workspace/')],cwd=R)
        assert hashlib.sha256(data).hexdigest()==h,rel
sampler=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R)
assert hashlib.sha256(sampler).hexdigest()==b['files']['min/src/sampler.rs']
print(f'PASS {len(m["files"])} source/evidence hashes; frozen native S2-variant Prepared constructor control checked with six normal-return child cuts. Whole S1/S6, initialization, SDK hash and release joins remain OPEN.')
