#!/usr/bin/env python3
"""Read-only audit of the first terminal24GiB partition; no proof replay."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-native-prepared-claim-memory24-terminal-v1'
j=json.loads((E/'collection.json').read_text())
assert j['source_only'] and not j['compiler_or_verifier_launched']
for rel,h in j['files'].items():
 p=E/rel
 assert p.suffix in ['.py','.json','.log','.txt']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
A=E/'v6/run-lo4'
r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
assert r['exit_status']==0 and r['source_unchanged'] and r['tools_unchanged'] and r['swaps']==0
assert r['cgroup']['memory.max']==str(24*2**30)
assert r['cgroup']['memory.high']==str(23*2**30)
assert r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M) for k in ['high','max','oom','oom_kill'])
assert r['command']==i['command']
c=r['command'];assert c[c.index('--harness')+1]=='verifier::proofs::prepared_new_claim_lo_point_4'
assert '--unwinding-assertions' in c and '--unwindset' in c
out=(A/'verify-stdout.log').read_text()
assert '0 of 3027 failed' in out and '2 of 3 cover properties satisfied' in out and 'VERIFICATION:- SUCCESSFUL' in out
assert json.loads((A/'outer-terminal.json').read_text())['exit_status']==0
assert json.loads((A/'terminal.json').read_text())['exit_status']==0
for n in ['admission-before-scope.json','verify-admission.json']:
 d=json.loads((A/n).read_text());assert d['admitted']
 assert d['finite_reserved_bytes']+d['additional_bytes']<d['limit_bytes']
 assert d['memory']['MemAvailable']>=d['remaining_capped_headroom_bytes']+4*2**30
p=json.loads((E/'v6/plan.json').read_text())
assert p['files']==i['source_pins']
assert json.loads((A/'compile-reuse.json').read_text())['source_pins_exact']
print(json.dumps(dict(status='PASS',pins=len(j['files']),accepted_partition='point4 columns0..14',whole_point4_closed=False,S1_or_S6_closed=False,source_context='historical25866; later unchanged selected bodies do not establish whole4bb3 transport')))
