#!/usr/bin/env python3
"""Audit pinned relative native eight-pair execution; no solver replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-query-pairs-cut-history-v1';S=E/'s1-query-pairs-cut-v6/source/query_pairs_cut_unrolled'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
collection=json.loads((P/'collection.json').read_text())
for p,h in collection['files'].items():assert sha(P/p)==h,p
plan=json.loads((T/'plan.json').read_text())
for p,h in plan['files'].items():assert sha(T/'binding.json' if p=='query-binding.json' else S/p)==h,p
frozen=lambda p:subprocess.check_output(['git','show',f'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/{p}'],cwd=R,text=True)
proof=(T/'proofs.rs').read_text();wrapper=(T/'wrapper.rs').read_text()
assert (S/'core-workspace/crates/aspis-core/src/r0_transcript.rs').read_text()==frozen('src/r0_transcript.rs')+wrapper+'\n#[cfg(kani)]mod s126_pairs_proofs{use super::*;\n'+proof+'\n}\n'
manifest=frozen('Cargo.toml');shim=json.loads((S/'driver-cargo-shim.json').read_text())
assert manifest.split('[dev-dependencies]\n')[1]==shim['removed_test_dependencies']
assert (S/'core-workspace/crates/aspis-core/Cargo.toml').read_text()==manifest.split('[dev-dependencies]\n')[0]
assert proof.count('#[kani::stub(')==2
for token in ['super::QueryScan::scan,super::s126_scan_reply','owned_block,super::s126_reference_scan_reply','let actual=super::queries_from_pairs(&blocks,&advances);','assert!(a[word]==b[word]);assert!(s[byte]==t[byte]);','assert!(a==b);','kani::assume(call<8);kani::assume(word<22);kani::assume(byte<32);','assert!(actual_calls==reference_calls);']:
 assert token in proof,token
for token in ['assert!(a[S126_OBS_WORD]==S126_WORD);assert!(n==S126_LEN);assert!(d==S126_DRAWS);assert!(block[S126_OBS_BYTE]==S126_BYTE);','S126_REFS+=1;S126_TAPE[index]','let (a,n,d,stop)=S126_TAPE[index];scan.accepted=a;scan.accepted_len=n;scan.draws=d;']:
 assert token in wrapper,token
# Frozen full native error datatype, not an acceptance-only carrier.
assert 'QuerySampleError::DrawLimitExhausted{accepted:scan.accepted_len,max_draws:64}' in proof
p=P/'v5/run-pairs';j=json.loads((p/'verify-receipt.json').read_text());i=json.loads((p/'verify-input.json').read_text())
assert j['exit_status']==0 and j['source_unchanged'] and j['tools_unchanged'] and j['swaps']==0
assert i['source_pins']==plan['files'] and i['command']==j['command']
cmd=j['command'];assert cmd[cmd.index('--features')+1]=='r0' and cmd[cmd.index('--harness')+1]=='r0_transcript::s126_pairs_proofs::pairs_cut_equal'
assert j['cgroup']['memory.max']==str(2*2**30) and j['cgroup']['memory.swap.max']=='0'
for key in ['high','max','oom','oom_kill']:assert re.search(r'^'+key+r' 0$',j['cgroup']['memory.events'],re.M)
o=(p/'verify-stdout.log').read_text();assert '0 of 673 failed' in o and '3 of 3 cover properties satisfied' in o and 'VERIFICATION:- SUCCESSFUL' in o
print(json.dumps(dict(status='PASS',pins=len(collection['files']),checks=673,full_state_scan_cuts=2,wall_seconds=j['wall_seconds'],peak_rss_kib=j['peak_rss_kib'],swap=0,scope='Relative native full eight-pair Result/trace equality. Requires concrete scan laws; no SDK/runtime/caller installation claimed.')))
