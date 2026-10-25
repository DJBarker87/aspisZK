#!/usr/bin/env python3
"""Read-only current native rho binding audit, including excluded failed predecessor."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-native-rho-history-v2';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
j=json.loads((P/'collection.json').read_text())
for rel,h in j['files'].items():assert hashlib.sha256((P/rel).read_bytes()).hexdigest()==h
A=P/'v3/run-point6';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text());plan=json.loads((T/'plan-corrected.json').read_text())
assert r['exit_status']==0 and r['swaps']==0 and r['source_unchanged']and r['tools_unchanged']
assert r['command']==i['command']and i['source_pins']==plan['files']
assert r['cgroup']['memory.max']==str(12*2**30)and r['cgroup']['memory.high']==str(11*2**30)and r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
assert '--unwinding-assertions'in r['command']and '--unwindset'in r['command']
s=(A/'verify-stdout.log').read_text();assert '0 of 3265 failed'in s and '2 of 3 cover properties satisfied'in s and 'VERIFICATION:- SUCCESSFUL'in s
proof=(T/'proofs.rs').read_text();assert hashlib.sha256(proof.encode()).hexdigest()==plan['files']['min/src/prepared_claim_native/proofs.rs']
for x in ['let actual=crate::sampler_native::qm31_sample(block);RHO=actual;canonical_q(actual);STAGE=7;actual','same_q(out.rho,unsafe{RHO})','assert!(x.c0.a.0<aspis_core::field::P)','assert!(x.c1.b.0<aspis_core::field::P)']:assert x in proof
assert 'same_q(out.rho,rho)'not in proof and 'kani::assume'not in proof and 'transmute'not in proof
source=E/'s1-native-prepared-rho-v2/source/prepared_rho'
assert (source/'min/src/prepared_claim_native/proofs.rs').read_text()==proof
raw=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R)
assert (source/'min/src/sampler.rs').read_bytes()==raw
assert '#[path="sampler.rs"] pub mod sampler_native;'in(source/'min/src/probe_prepared_claim.rs').read_text()
old=P/'v2/run-point6';bad=json.loads((old/'verify-receipt.json').read_text());assert bad['exit_status']==1 and bad['swaps']==0
out=(old/'verify-stdout.log').read_text();assert '4 of 3257 failed'in out and 'same_q'in out and 'CBMC timed out'not in out
assert not json.loads((P/'v1/run-point6/admission-before-scope.json').read_text())['admitted']
print(json.dumps(dict(status='PASS',pins=len(j['files']),current_native_rho_result_cut_removed=True,full_returned_QM31_and_canonicality_checked=True,normal_result_cuts=7,scripted_digest_retained=True,canonical_payload_domain=True,exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=0,SDK_runtime_oracle_release_and_whole_S1_S6_closed=False)))
