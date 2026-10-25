#!/usr/bin/env python3
"""Both actual-decoder native gates, with explicit canonical-input domain."""
from pathlib import Path
import runpy,json,hashlib,re
T=Path(__file__).resolve().parent;runpy.run_path(str(T/'check.py'),run_name='__main__')
R=T.parents[1];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-native-prepared-field-terminal-v2'
j=json.loads((E/'collection.json').read_text())
for rel,h in j['files'].items():assert hashlib.sha256((E/rel).read_bytes()).hexdigest()==h
rows=[]
for v,point in [(1,6),(2,5)]:
 A=E/f'v{v}/run-point{point}';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
 assert r['command']==i['command']and i['source_pins']==json.loads((T/'plan.json').read_text())['files']
 assert r['cgroup']['memory.max']==str(24*2**30)and r['cgroup']['memory.high']==str(23*2**30)and r['cgroup']['memory.swap.max']=='0'
 assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
 assert '--unwinding-assertions'in r['command']and '--unwindset'in r['command']
 assert r['command'][r['command'].index('--harness')+1]==f'verifier::proofs::prepared_new_claim_point_{point}'
 o=(A/'verify-stdout.log').read_text();assert '0 of 3267 failed'in o and '2 of 3 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
 rows.append(dict(point=point,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],cgroup_peak=r['cgroup']['memory.peak']))
s=(T/'proofs.rs').read_text();assert '29*POINT+(kani::any::<u8>()%29)as usize'in s
assert {n%29 for n in range(256)}==set(range(29))
print(json.dumps(dict(status='PASS',pins=len(j['files']),accepted=['all29 point5 positions','full success6'],metrics=rows,normal_primitive_cuts=8,domain='canonical928-byte payload; no arbitrary malformed-input totality',S1_S6_closed=False,source_context='historical25866; current full-source check pending')))
