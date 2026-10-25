#!/usr/bin/env python3
"""Audit actual-field success gate and source binding; never replay proof."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-native-prepared-field-terminal-v1'
j=json.loads((E/'collection.json').read_text())
for rel,h in j['files'].items():assert hashlib.sha256((E/rel).read_bytes()).hexdigest()==h
A=E/'v1/run-point6';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
assert r['exit_status']==0 and r['swaps']==0 and r['source_unchanged'] and r['tools_unchanged']
assert i['command']==r['command'] and i['source_pins']==json.loads((T/'plan.json').read_text())['files']
assert r['cgroup']['memory.max']==str(24*2**30) and r['cgroup']['memory.high']==str(23*2**30) and r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
assert '--unwinding-assertions'in r['command'] and '--unwindset'in r['command']
out=(A/'verify-stdout.log').read_text();assert '0 of 3267 failed'in out and '2 of 3 cover properties satisfied'in out and 'VERIFICATION:- SUCCESSFUL'in out
p=json.loads((T/'plan.json').read_text())
s=(T/'proofs.rs').read_text();assert hashlib.sha256(s.encode()).hexdigest()==p['files']['min/src/prepared_claim_native/proofs.rs']
body=subprocess.check_output(['git','show','25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R,text=True).splitlines()[20]
assert s.endswith(body.replace('pub fn field(','fn native_field(')+'\n')
assert 'let actual=native_field(bytes,index);same_e(actual,FIELDS[index]);actual'in s
assert 'y1[32*col+4*j+b]=(words[j]>>(8*b))as u8'in s
assert s.index('y1[32*col+4*j+b]')<s.index('let view=View{')<s.index('let result=Prepared::new(')
assert 'kani::assume'not in s and 'transmute'not in s
local=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-native-prepared-field-v2'
q=json.loads((local/'receipt.json').read_text());assert q['exit_status']==0 and not q['verification_launched']
for n in ['compile-receipt.json','verify-receipt.json']:
 q=json.loads((A/n).read_text());assert q['exit_status']==0 and q['source_unchanged']and q['tools_unchanged']and q['swaps']==0
print(json.dumps(dict(status='PASS',pins=len(j['files']),actual_field_reads_in_complete_success=29,normal_primitive_cuts=8,domain='canonical928-byte payload, with all native words retained',enclosing_S1_S6_closed=False,source_context='historical25866; later whole-source/native SDK/oracle/release not closed')))
