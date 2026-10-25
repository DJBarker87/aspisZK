#!/usr/bin/env python3
"""Read-only relative native block/source audit; no solver replay or implicit caller installation."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-query-block-cut-history-v2';plan=json.loads((T/'plan.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((P/'collection.json').read_text())
for p,h in j['files'].items():assert sha(P/p)==h
src=E/'s1-query-block-cut-v3/source/query_block_cut_observed'
for p,h in plan['files'].items():assert sha(T/'binding.json'if p=='query-binding.json'else src/p)==h
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/r0_transcript.rs'],cwd=R,text=True)
assert(src/'core-workspace/crates/aspis-core/src/r0_transcript.rs').read_text()==frozen+(T/'wrapper.rs').read_text()
assert 'let stop=scan.scan(block);'in(T/'wrapper.rs').read_text()
proof=(T/'proofs.rs').read_text();assert proof==(src/'min/src/probe_block.rs').read_text()
assert proof.count('#[kani::stub(')==2
for text in ['#[kani::stub(<[u32]>::contains,contains_reply)]','#[kani::stub(crate::owned_contains,owned_contains_reply)]','T:PartialEq+Copy+Into<u32>','assert!(x[observed_cell]==y[observed_cell]);','assert!(CALLS==REF_CALLS);','if index==OBS_CALL','assert!(len==OBS_LEN);assert!(candidate==OBS_CANDIDATE);','if OBS_CELL<len{assert!(a[OBS_CELL]==OBS_VALUE);}']:
 assert text in proof,text
assert 'transmute'not in proof and proof.count('CALLS+=1;REPLIES[index]')==2
# The observed coordinates inspect ghosts only; reply selection remains index-only.
assert 'kani::assume(observed_call<8);kani::assume(observed_cell<22);'in proof
reference=E/'s1-query-block-extraction-v1/v3/src/lib.rs'
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
for k in ['fn owned_contains(','fn owned_step(','fn owned_block(']:assert item(proof,k)==item(reference.read_text(),k)
a=P/'v2/run-pairs';r=json.loads((a/'verify-receipt.json').read_text());i=json.loads((a/'verify-input.json').read_text())
assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
assert i['source_pins']==plan['files']and i['command']==r['command']
assert r['command'][r['command'].index('--solver')+1]=='cadical'
assert r['cgroup']['memory.max']==str(4*2**30)and r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
o=(a/'verify-stdout.log').read_text();assert '0 of 868 failed'in o and '2 of 2 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
bad=json.loads((P/'v1/run-pairs/verify-receipt.json').read_text());assert bad['exit_status']==1 and 'CBMC timed out'in(P/'v1/run-pairs/verify-stdout.log').read_text()
print(json.dumps(dict(status='PASS',pins=len(j['files']),native_loop_and_word_decoder_execute=True,membership_cuts=2,universal_observer_call=8,universal_observer_cell=22,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=0,remaining='Compose exact pure membership laws andpointwise trace extensionality; native eight-pair driver/caller/SDK/runtime/release remain separate. Relative block check only.')))
