#!/usr/bin/env python3
from pathlib import Path
import json,re,statistics,sys
E=Path(sys.argv[1]);out={}
def stats(v):
 s=sorted(v);return {'n':len(s),'median':statistics.median(s),'min':min(s),'max':max(s),'range':max(s)-min(s),'mean':statistics.mean(s),'sample_stdev':statistics.stdev(s) if len(s)>1 else None}
for mode in ['research','v2']:
 O=E/'receipts'/(mode+'-run');rows=[json.loads(l.removeprefix('SPEED_ROW ')) for l in (O/'stdout.log').read_text().splitlines() if l.startswith('SPEED_ROW ')]
 checks=[];reservations=[];split=None
 for l in (O/'stderr.log').read_text().splitlines():
  if l.startswith('SPEED_RESERVATION '):reservations.append(float(l.split()[1]))
  if l.startswith('SPEED_CHECK_SPLIT '):split=list(map(float,l.split()[1:]))
  if l.startswith('SPEED_CHECK '):
   a=list(map(float,l.split()[1:]));checks.append(dict(zip(['public_data','emit','convert_build','check'],a))|({'convert':split[0],'build':split[1]} if split else {}));split=None
 assert len(rows)==10 and sum(r['attempts'] for r in rows)==len(reservations)==len(checks)
 at=0
 for r in rows:
  n=r['attempts'];r['p_r1_split']={k:sum(c[k] for c in checks[at:at+n]) for k in checks[at]};r['reservation_seconds']=sum(reservations[at:at+n]);at+=n
  p=r['phases_inclusive_exclusive_calls'];r['exclusive_sum']=sum(v[1] for v in p.values());assert abs(r['exclusive_sum']-r['wall_seconds'])<0.001
  assert r['verified_strict_dense'] and r['proof_bytes']==57607
 out[mode]={'per_run':rows,'fixtures':{}}
 for fixture in ['transfer','withdrawal']:
  rs=[r for r in rows if r['fixture']==fixture];assert len(rs)==5
  out[mode]['fixtures'][fixture]={'wall_seconds':stats([r['wall_seconds'] for r in rs]),'attempts':[r['attempts'] for r in rs],'phase_inclusive':{k:stats([r['phases_inclusive_exclusive_calls'][k][0] for r in rs]) for k in rs[0]['phases_inclusive_exclusive_calls']},'phase_exclusive':{k:stats([r['phases_inclusive_exclusive_calls'][k][1] for r in rs]) for k in rs[0]['phases_inclusive_exclusive_calls']},'p_r1_split':{k:stats([r['p_r1_split'][k] for r in rs]) for k in rs[0]['p_r1_split']},'reservation_seconds':stats([r['reservation_seconds'] for r in rs])}
(E/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
for mode in out:
 for f,x in out[mode]['fixtures'].items():print(mode,f,x['wall_seconds'],x['attempts'])
