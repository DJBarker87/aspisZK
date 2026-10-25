#!/usr/bin/env python3
"""Read-only scope/hash guard; no unchanged proof replay."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-terminal-selector-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
frozen=subprocess.check_output(['git','show','25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'],cwd=R,text=True)
assert 'let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);' in frozen
source=B/'evidence/terminal-qm31-fromfn-copy-candidate-v3-20261019/crates/aspis-statement/src/lib.rs'
text=source.read_text();a=text.index('#[inline(always)]\npub(crate) fn array_from_fn_copy');z=text.index('\n#[cfg(test)]',a);helper=text[a:z]
selector=(R/'tools/s1-terminal-selector-20261025/selector.rs').read_text()
assert helper in selector
assert 'fn native_selector(claims:&[[QM31;29];3])->[QM31;84]{core::array::from_fn(|i| claims[i / 28][i % 28])}' in selector
for n in range(1,5):
    A=E/f's1-terminal-selector-v{n}';i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
    for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
    assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
    assert r['swaps']==0 and r['watchdog_stop'] is None and r['host_SSH_operations']==0
    assert 'uninit-checks' not in r['command'] and '--unwinding-assertions' in r['command']
    for p in (A/'source').rglob('*'):
        if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
    assert (A/'source/min/src/terminal_selector.rs').read_text()==selector
    proof=(A/'source/min/src/terminal_selector_proofs.rs').read_text()
    assert 'kani::assume' not in proof and 'kani::stub' not in proof
    assert '#[kani::unwind(85)]' in proof
    log=(A/'stdout.log').read_text()
    if n==2:
        assert r['exit_status']==0 and r['verification_launched']
        assert '0 of 143 failed' in log and 'VERIFICATION:- SUCCESSFUL' in log
    elif n==4:
        assert r['exit_status']==1 and r['verification_launched']
        assert '1 of ' in log and 'VERIFICATION:- FAILED' in log
        assert 'input[2][27].c1.b.0' in log
    else:assert r['exit_status']==0 and not r['verification_launched']
print(f'PASS {len(m["files"])} hashes; pure native Terminal selector84/copy equality checked; negative last-word control fails; whole Terminal/native installation OPEN')
