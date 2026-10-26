#!/usr/bin/env python3
"""Audit native query-driver constructor candidate; success requires terminal evidence."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P=E/'s1-native-query-full-terminal-v2'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((P/'collection.json').read_text())
for p,h in c['files'].items():assert sha(P/p)==h,p
local=E/'s1-native-prepared-query-full-v1';j=json.loads((local/'receipt.json').read_text());i=json.loads((local/'input.json').read_text())
assert j['exit_status']==0 and j['swaps']==0 and not j['verification_launched'] and not j['watchdog_stop']
S=local/'source/prepared_query_full_v1';plan=json.loads((T/'plan-full-observer-bound.json').read_text())
for rel,h in plan['files'].items():
 p=S/rel
 if rel=='query-driver-binding.json':p=T/'binding-full.json'
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
s=(T/'proofs-full.rs').read_text();assert (S/'min/src/prepared_claim_native/proofs.rs').read_text()==s
for v in ['let actual=aspis_core::r0_transcript::s126_queries_from_pairs(blocks,advances);','QUERY=q;STATES[5]=next;','Err(_)=>{FAIL_AT=0;}','let fail_at=unsafe{FAIL_AT};','out.queries[i]==unsafe{QUERY[i]}']:
 assert v in s,v
assert 'kani::stub(aspis_core::r0_transcript::QueryScan' not in s and 'kani::assume' not in s
assert s.count('#[kani::unwind(33)]')==7
assert 'else{Ok((QUERY,STATES[5]))}' not in s
# These are retained failures, not an accepted full-stage proof.
for n,why in [('v1','any_array<33>'),('v2','verifier::proofs::same_bytes'),('v3','CBMC timed out')]:
 p=P/n/'run-point6';r=json.loads((p/'verify-receipt.json').read_text());v=json.loads((p/'verify-input.json').read_text())
 assert r['exit_status']==1 and r['source_unchanged'] and r['tools_unchanged'] and r['swaps']==0
 assert v['source_pins']==plan['files'] and v['command']==r['command']
 assert r['cgroup']['memory.max']==str(12*2**30) and r['cgroup']['memory.high']==str(11*2**30) and r['cgroup']['memory.swap.max']=='0'
 for k in ['high','max','oom','oom_kill']:assert re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)
 o=(p/'verify-stdout.log').read_text();assert why in o and 'VERIFICATION:- SUCCESSFUL' not in o
 assert '--unwinding-assertions'in r['command']
 if n!='v1':assert json.loads((p/'compile-reuse.json').read_text())['compiler_replayed']==False
 if n=='v3':assert ':34,'in r['command'][-1] and ':225'in r['command'][-1]
print(json.dumps(dict(status='EVIDENCE_AUDIT_PASS',uncut_enclosing_verification='NOT_ESTABLISHED',reason='Two explicit harness unwinding failures then304.6s timeout, no memory pressure/swap. No unchanged larger-cap retry. Use checked callee composition.')))
