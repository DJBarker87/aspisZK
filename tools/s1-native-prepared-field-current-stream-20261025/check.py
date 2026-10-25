#!/usr/bin/env python3
"""Read-only current-source/native gate audit. No compiler or proof replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-native-current-stream-terminal-v1';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
j=json.loads((P/'collection.json').read_text());plan=json.loads((T/'plan.json').read_text())
for rel,h in j['files'].items():assert hashlib.sha256((P/rel).read_bytes()).hexdigest()==h
assert json.loads((P/'v1/plan.json').read_text())==plan and plan['source_freeze']==F
source=E/'s1-native-prepared-field-current-stream-v1/source/prepared_field_current_stream'
core=[p for p in (source/'core-workspace/crates/aspis-core').rglob('*')if p.is_file()];assert len(core)==88
assert sum(p.suffix=='.rs'for p in core)==87
for p in core:
 raw=subprocess.check_output(['git','show',F+':'+str(p.relative_to(source/'core-workspace'))],cwd=R)
 assert raw==p.read_bytes(),str(p)
# Full selected native definitions originate in the exact current frozen source.
old=json.loads((source/'predecessor-binding.json').read_text())
for key,row in old['selected_spans'].items():
 raw=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/'+row['file']],cwd=R,text=True)
 assert old['selected'][key]in raw,key
helpers=json.loads((R/'tools/s1-native-prepared-claim-20261025/source-binding.json').read_text())['dot_helpers']
base=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/fast_pairing.rs'],cwd=R,text=True)
assert (source/'min/src/prepared_claim_native/fast_pairing.rs').read_text()==base.replace(helpers['insertion_after'],helpers['insertion_after']+helpers['insertion'],1)+helpers['append']
s=(T/'proofs.rs').read_text();assert hashlib.sha256(s.encode()).hexdigest()==plan['files']['min/src/prepared_claim_native/proofs.rs']
assert 'DOT_WORDS'not in s and 'DOT_COUNTS'not in s and 'kani::assume'not in s and 'transmute'not in s
for text in ['let words=kani::any::<[u64;8]>()','let count=kani::any::<usize>()','proof_input(words,count)','DOT_LAST[i]','DOT_COUNT_LAST','let actual=native_field(bytes,index);same_e(actual,FIELDS[index]);actual']:
 assert text in s,text
metrics=[]
for point in [5,6]:
 A=P/f'v1/run-point{point}';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
 assert i['source_pins']==plan['files']and i['command']==r['command']
 assert r['cgroup']['memory.max']==str(24*2**30)and r['cgroup']['memory.high']==str(23*2**30)and r['cgroup']['memory.swap.max']=='0'
 assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
 assert '--unwinding-assertions'in r['command']and '--unwindset'in r['command']
 assert r['command'][r['command'].index('--harness')+1]==f'verifier::proofs::prepared_new_claim_point_{point}'
 o=(A/'verify-stdout.log').read_text();assert '0 of 3191 failed'in o and '2 of 3 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
 metrics.append({k:r[k]for k in ['wall_seconds','peak_rss_kib','swaps']})
assert json.loads((P/'v1/run-point6/terminal.json').read_text())['exit_status']==0
print(json.dumps(dict(status='PASS',pins=len(j['files']),current_core_package_files=88,Rust_source_files=87,current_selected_definitions=len(old['selected_spans']),accepted=['all29 point5 positions','full success6'],metrics=metrics,normal_primitive_cuts=8,scripted_digest_parameter_retained=True,canonical928_byte_input_domain=True,full_native_dot_carrier=True,whole_S1_S6_or_release_closed=False)))
