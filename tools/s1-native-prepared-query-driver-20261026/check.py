#!/usr/bin/env python3
"""Audit native query-driver constructor candidate; success requires terminal evidence."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P=E/'s1-native-query-driver-terminal-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((P/'collection.json').read_text())
for p,h in c['files'].items():assert sha(P/p)==h,p
local=E/'s1-native-prepared-query-driver-v1';j=json.loads((local/'receipt.json').read_text());i=json.loads((local/'input.json').read_text())
assert j['exit_status']==0 and j['swaps']==0 and not j['verification_launched'] and not j['watchdog_stop']
S=local/'source/prepared_query_driver_v2';plan=json.loads((T/'plan.json').read_text())
for rel,h in plan['files'].items():
 p=S/rel
 if rel=='query-driver-binding.json':p=T/'binding.json'
 assert sha(p)==h,rel
frozen=subprocess.check_output(['git','show',F+':crates/aspis-core/src/r0_transcript.rs'],cwd=R,text=True)
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
original=item(frozen,'pub fn queries_from_pairs(')
twin=original.replace('pub fn queries_from_pairs(','pub fn s126_queries_from_pairs(',1)
wrapper=(R/'tools/s1-query-pairs-cut-20261025/wrapper.rs').read_text()
assert (S/'core-workspace/crates/aspis-core/src/r0_transcript.rs').read_text()==frozen+'\n#[cfg(kani)]\n'+twin+'\n'+wrapper
s=(T/'proofs.rs').read_text();assert (S/'min/src/prepared_claim_native/proofs.rs').read_text()==s
for v in ['let actual=aspis_core::r0_transcript::s126_queries_from_pairs(blocks,advances);','QUERY=q;STATES[5]=next;','Err(_)=>{FAIL_AT=0;}','let fail_at=unsafe{FAIL_AT};','out.queries[i]==unsafe{QUERY[i]}']:
 assert v in s,v
assert s.count('#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]')==7
assert 'else{Ok((QUERY,STATES[5]))}' not in s
p=P/'v1/run-point6';r=json.loads((p/'verify-receipt.json').read_text());v=json.loads((p/'verify-input.json').read_text())
assert r['exit_status']==0 and r['source_unchanged'] and r['tools_unchanged'] and r['swaps']==0
assert v['source_pins']==plan['files'] and v['command']==r['command']
assert r['cgroup']['memory.max']==str(12*2**30) and r['cgroup']['memory.high']==str(11*2**30) and r['cgroup']['memory.swap.max']=='0'
for k in ['high','max','oom','oom_kill']:assert re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)
o=(p/'verify-stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL'in o and re.search(r'0 of \d+ failed',o)
assert '--unwinding-assertions'in r['command'] and '--unwindset'in r['command']
print(json.dumps(dict(status='PASS',scope='Complete native constructor/claim and exact native query driver; bounded scan-state + unchanged sampler/arithmetic/dot cuts. Query result and selected state are same actual driver output. No whole S1/SDK/runtime/release closure.',wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=0)))
