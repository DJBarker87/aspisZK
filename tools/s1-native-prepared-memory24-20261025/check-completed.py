#!/usr/bin/env python3
"""Read-only source-only audit; union checked native error-position partitions."""
from pathlib import Path
import hashlib,json,sys,re
R=Path(__file__).resolve().parents[2];label=sys.argv[1]
assert re.fullmatch(r's1-native-prepared-claim-memory24-completed-v[0-9]+',label)
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'/label
j=json.loads((E/'collection.json').read_text())
assert j['source_only'] and not j['compiler_or_verifier_launched']
for rel,h in j['files'].items():
 p=E/rel;assert p.suffix in ['.py','.json','.log','.txt']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
plan=json.loads((E/'v6/plan.json').read_text())
accepted=[];metrics=[];covered={4:set(),5:set()}
for A in sorted((E/'v6').glob('run-*')):
 case=A.name[4:];assert case in ['lo4','hi4','lo5','hi5']
 terminal=json.loads((A/'outer-terminal.json').read_text())
 if terminal['exit_status']!=0:continue
 r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged'] and r['tools_unchanged'] and r['swaps']==0
 assert i['source_pins']==plan['files'] and i['command']==r['command']
 assert r['cgroup']['memory.max']==str(24*2**30) and r['cgroup']['memory.high']==str(23*2**30)
 assert r['cgroup']['memory.swap.max']=='0'
 assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
 c=r['command'];assert c[c.index('--harness')+1]=='verifier::proofs::prepared_new_claim_'+case[:2]+'_point_'+case[2:]
 assert '--unwinding-assertions' in c and '--unwindset' in c
 assert c[c.index('--unwindset')+1].endswith('.2:8')
 out=(A/'verify-stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL' in out and re.search(r'0 of [0-9]+ failed',out)
 assert '2 of 3 cover properties satisfied' in out
 for n in ['admission-before-scope.json','verify-admission.json']:
  d=json.loads((A/n).read_text());assert d['admitted']
  assert d['finite_reserved_bytes']+d['additional_bytes']<d['limit_bytes']
  assert d['memory']['MemAvailable']>=d['remaining_capped_headroom_bytes']+4*2**30
 accepted.append(case);point=int(case[2:]);base,width=(0,15)if case[:2]=='lo'else(15,14)
 actual={base+x%width for x in range(256)};assert actual==set(range(base,base+width));covered[point]|=actual
 metrics.append(dict(case=case,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],cgroup_peak=r['cgroup']['memory.peak']))
result=dict(status='PASS',pins=len(j['files']),accepted=accepted,fully_checked_error_points=[p for p in covered if covered[p]==set(range(29))],remaining_columns={p:sorted(set(range(29))-covered[p])for p in covered},metrics=metrics,enclosing_S1_S6_closed=False,normal_primitive_cuts=9,source_context='historical25866 native component; no whole4bb3 or SDK/runtime/extraction/oracle/release closure')
print(json.dumps(result))
