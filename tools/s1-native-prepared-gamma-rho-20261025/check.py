#!/usr/bin/env python3
"""Source-only audit of two real sampler bodies in current native caller; no replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-native-gamma-rho-history-v1';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
j=json.loads((P/'collection.json').read_text())
for p,h in j['files'].items():assert hashlib.sha256((P/p).read_bytes()).hexdigest()==h
A=P/'v1/run-point6';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text());plan=json.loads((T/'plan.json').read_text())
assert r['exit_status']==0 and r['swaps']==0 and r['source_unchanged']and r['tools_unchanged']
assert r['command']==i['command']and i['source_pins']==plan['files']
assert r['cgroup']['memory.max']==str(12*2**30)and r['cgroup']['memory.high']==str(11*2**30)and r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
o=(A/'verify-stdout.log').read_text();assert '0 of 3589 failed'in o and '2 of 3 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
assert '--unwinding-assertions'in r['command']and '--unwindset'in r['command']
s=(T/'proofs.rs').read_text();assert hashlib.sha256(s.encode()).hexdigest()==plan['files']['min/src/prepared_claim_native/proofs.rs']
for text in ['crate::sampler_native::gamma_sample(block)','SCALARS[0]=actual;canonical_e(actual)','actual.to_limbs().iter().any(|&x|x!=0)','same_e(out.gamma,unsafe{SCALARS[0]})','crate::sampler_native::qm31_sample(block)','same_q(out.rho,unsafe{RHO})']:assert text in s
assert 'kani::assume'not in s and 'transmute'not in s
source=E/'s1-native-prepared-gamma-rho-v1/source/prepared_gamma_rho'
assert(source/'min/src/prepared_claim_native/proofs.rs').read_text()==s
assert(source/'min/src/sampler.rs').read_bytes()==subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R)
print(json.dumps(dict(status='PASS',pins=len(j['files']),native_gamma_and_rho_result_cuts_removed=True,gamma_nonzero_and_all8_words_canonical=True,rho_all4_words_canonical=True,normal_primitive_result_cuts=6,scripted_digest_and_canonical_payload_domain_retained=True,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=0,whole_S1_S6_or_release_closed=False)))
