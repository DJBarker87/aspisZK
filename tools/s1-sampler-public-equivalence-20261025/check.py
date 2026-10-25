#!/usr/bin/env python3
"""Read-only full native public-value equality/source audit; no solver replay."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-sampler-public-history-v1';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
j=json.loads((P/'collection.json').read_text());plan=json.loads((T/'plan.json').read_text())
for p,h in j['files'].items():assert hashlib.sha256((P/p).read_bytes()).hexdigest()==h
src=E/'s1-sampler-public-equivalence-v1/source/sampler_public_equivalence'
actual=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R)
assert(src/'min/src/equality_actual.rs').read_bytes()==actual
assert(src/'min/src/equality_reference.rs').read_bytes()==(T/'reference.rs').read_bytes()
assert(src/'min/src/probe_public.rs').read_bytes()==(T/'proofs.rs').read_bytes()
refpath=B/'lean-candidates/post25-indexed-addsmall-source-model-20261020/extraction/candidate-input/lib.rs';reference=refpath.read_text()
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
for k in ['fn qm31_div_pass(','fn low_base_p_digits(','fn decode8(','fn add_small_base_p(','pub fn ordinary_sample(','pub fn gamma_sample(']:assert item(reference,k)in(T/'reference.rs').read_text()
core=subprocess.check_output(['git','show',F+':crates/aspis-core/src/field/wide_exact.rs'],cwd=R,text=True)
for k in ['pub fn new(c0: QM31, c1: QM31)','fn canonical_qm31(']:assert ''.join(item(reference,k).split())==''.join(item(core,k).split())
assert 'use aspis_core::field::'in(T/'reference.rs').read_text()
proof=(T/'proofs.rs').read_text();assert all(x not in proof for x in ['kani::stub','kani::assume','transmute'])
assert 'while j<8{assert!(a[j]==b[j]);j+=1;}'in proof
metrics=[]
for case,checks in [('ordinary',353),('gamma',430)]:
 A=P/('v1/run-'+case);r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
 assert r['command']==i['command']and i['source_pins']==plan['files']and r['command'][r['command'].index('--solver')+1]=='z3'
 assert any(k.endswith('/z3-tool-v1/bin/z3')for k in i['tool_pins'])
 o=(A/'verify-stdout.log').read_text();assert f'0 of {checks} failed'in o and '1 of 1 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
 assert r['cgroup']['memory.max']==str(12*2**30)and r['cgroup']['memory.swap.max']=='0'
 assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
 metrics.append(dict(case=case,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=0))
print(json.dumps(dict(status='PASS',pins=len(j['files']),actual_vs_owned_full8_word_value_equality=True,domain='all32-byte blocks',result_stubs=0,actual_core_constructor_source_matched=True,metrics=metrics,whole_S1_S6_SDK_oracle_release_not_closed=True)))
