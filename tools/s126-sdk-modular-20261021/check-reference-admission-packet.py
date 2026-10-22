#!/usr/bin/env python3
"""Check the conditional reference admission packet, without solver replay."""
from pathlib import Path
import json,hashlib,tomllib
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'sdk-reference-admission';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
m=read(P/'manifest.json');assert m['schema']=='focused-extractor-proof-packet-v1'
assert set(m['files'])=={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file() and p.name!='manifest.json'}
for n,h in m['files'].items():
 p=P/n;assert sha(p)==h,n
 assert p.suffix in ['.json','.log','.py','.rs','.toml','.lock'],n
q=read(P/'qualification.json');cut=read(P/'source/source-cut.json')
assert q['source_sha256']==cut['source_sha256']==sha(P/'source/src/lib.rs')
assert q['cargo_lock_sha256']==sha(P/'source/Cargo.lock')
inp=read(P/'sdk-reference-admission-check-v1-input.json')
assert inp['source_sha256']==q['source_sha256']
assert inp['runner_sha256']==sha(P/'runner/run-modular-host.py')
assert '--unwinding-assertions' in inp['command'] and '--property' not in inp['command']
assert inp['command'][inp['command'].index('--harness-timeout')+1]=='180'
r=read(P/'receipt/receipt.json')
assert r['exit_status']==0 and r['swaps']==0
assert r['limits']['memory.max']=='8589934592' and r['limits']['memory.swap.max']=='0'
log=(P/'receipt/stdout.log').read_text()
assert '** 0 of 1722 failed' in log and '** 2 of 2 cover properties satisfied' in log
assert 'Complete - 1 successfully verified harnesses, 0 failures, 1 total.' in log
rows=[h for h in read(P/'harness-metadata.json')['proof_harnesses'] if h['pretty_name']=='proofs::reference_admission']
assert len(rows)==1 and rows[0]['crate_name']=='aspis_s126_sdk_reference_admission'
assert not rows[0]['attributes'].get('verified_stubs')
assert len(rows[0]['attributes']['stubs'])==5
old=E/'sdk-parent-cuts/sources/owned-sdk-borrowed-v1/src/lib.rs'
assert sha(old)==sha(P/'dependencies/aspis-s126-owned-sdk-borrowed/src/lib.rs')
for name,dep in q['dependency_source_pins'].items():
 for rel,h in dep['files'].items():assert sha(P/'dependencies'/name/rel)==h
s=(P/'source/src/lib.rs').read_text()
assert 'let data_slots=[proof_slot,1,2];' in s
assert 'let counts:[isize;3]=kani::any();kani::assume(counts[2]==0);kani::assume(counts[1]>=0 && counts[1]<isize::MAX);' in s
for length in [58295,1880,1768]:assert f'kani::vec::exact_vec::<u8,{length}>()' in s
assert 'let (result,out)=owned::owned_stage1(program,model,vec![3,split]);' in s
assert tomllib.loads((P/'source/Cargo.toml').read_text())['package']['name']=='aspis-s126-sdk-reference-admission'
print(json.dumps(dict(target='proofs::reference_admission',exit_status=0,noncover_checks=1722,reached_covers=2,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=0,qualification=q['result']),indent=2))
