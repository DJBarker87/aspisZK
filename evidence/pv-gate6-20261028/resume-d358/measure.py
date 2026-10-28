"""Ten alternating pairs; exact native harness; no source instrumentation."""
from pathlib import Path
import os,sys,json,time,subprocess,hashlib,statistics
H=Path(__file__).resolve().parent.parent;R=Path(__file__).resolve().parent;O=R/'measurement';O.mkdir()
MARKER=H.parent/'QUIET_WINDOW.json';OWNER='stream-b-pv-gate6'
CPUS='0-21';PLANNED=10;MIN_UNTHROTTLED=10
BIN={'control':H/'combined/baseline/bin/prover_rw_gate','candidate':H/'bin/prover_rw_gate'}
REV={'control':'c57a344726745387efb38d1571d885c69ce829ee','candidate':'82566acdfb488183022f41ac564c11df22c9404f'}
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot(label):
 x=dict(utc=time.time(),label=label,package_temperatures_millidegrees={},thermal_counters={},read_errors={},loadavg=Path('/proc/loadavg').read_text(),affinity=CPUS)
 for p in Path('/sys/class/hwmon').glob('hwmon*'):
  name=(p/'name').read_text().strip()
  for lab in p.glob('temp*_label'):
   if 'Package' in lab.read_text():
    inp=lab.with_name(lab.name.replace('_label','_input'))
    try:x['package_temperatures_millidegrees'][name+'/'+lab.read_text().strip()]=int(inp.read_text())
    except OSError as e:x['read_errors'][str(inp)]=repr(e)
 for p in Path('/sys/devices/system/cpu').glob('cpu[0-9]*/thermal_throttle/*'):
  try:x['thermal_counters'][str(p)]=int(p.read_text())
  except OSError as e:x['read_errors'][str(p)]=repr(e)
 write(O/(label+'.json'),x)
 return x

def guard(label):
 r=subprocess.run(['python3',str(R/'quiet-preflight.py'),str(O/(label+'-guard.json'))],stdout=subprocess.DEVNULL)
 assert r.returncode in (0,78),('scope inventory failure',label,r.returncode)
 m=json.loads(MARKER.read_text());assert m['owner']==OWNER and time.time()<m['until'],'window expired'
 return r.returncode==0

def compare(i,coin):
 rows=[]
 for f in ['transfer','withdrawal']:
  roots={w:O/w/f'pair-{i}'/f'{f}-{coin}' for w in BIN};files={}
  for n in ['proof.bin','public.bin']:
   v={w:(p/n).read_bytes() for w,p in roots.items()};files[n]=dict(identical=len(set(v.values()))==1,**{w:dict(sha256=sha(b),bytes=len(b)) for w,b in v.items()})
  records={w:json.loads((p/'result.json').read_text()) for w,p in roots.items()}
  canonical={w:json.dumps({k:v for k,v in r.items() if k!='seconds'},sort_keys=True,separators=(',',':')) for w,r in records.items()}
  ledgers={w:{str(q.relative_to(p/'ledger')):dict(sha256=sha(q.read_bytes()),bytes=q.stat().st_size) for q in (p/'ledger').rglob('*') if q.is_file()} for w,p in roots.items()}
  row=dict(pair=i,coin=coin,fixture=f,files=files,records=records,canonical_result_identical=len(set(canonical.values()))==1,canonical_records=canonical,ledger_identical=ledgers['control']==ledgers['candidate'],ledger_manifest=ledgers)
  rows.append(row)
 write(O/f'comparison-pair-{i}.json',rows)
 assert all(all(v['identical'] for v in r['files'].values()) and r['canonical_result_identical'] and r['ledger_identical'] for r in rows),('BYTE DISAGREEMENT',coin)
 return rows

pins=json.loads((H/'timing-binary-pins.json').read_text())
for w,b in BIN.items():assert sha(b.read_bytes())==pins[w]['sha256'],('binary changed',w)
pairs=[];error=None;start=time.time();consecutive_invalid=0;stop_reason=None
try:
 for i in range(PLANNED):
  # A full pair contains four proofs; reserve conservative remaining time.
  m=json.loads(MARKER.read_text());assert time.time()+120<m['until'],'insufficient window for next pair'
  coin=100+i;order=['control','candidate'] if i%2==0 else ['candidate','control']
  valid=guard(f'pair-{i}-before')
  before=snapshot(f'pair-{i}-before');assert before['package_temperatures_millidegrees'] and before['thermal_counters'] and not before['read_errors'],'thermal telemetry incomplete'
  for w in order:
   valid=guard(f'pair-{i}-{w}-before') and valid
   cmd=['taskset','--cpu-list',CPUS,str(BIN[w]),str(O/w/f'pair-{i}'),str(coin),'1']
   with (O/f'pair-{i}-{w}.stdout.log').open('w') as so,(O/f'pair-{i}-{w}.stderr.log').open('w') as se:
    r=subprocess.run(['/usr/bin/time','-v','-o',str(O/f'pair-{i}-{w}.time.log'),*cmd],stdout=so,stderr=se,timeout=max(1,m['until']-time.time()-2))
   assert r.returncode==0,(i,w,r.returncode)
   valid=guard(f'pair-{i}-{w}-after') and valid
  after=snapshot(f'pair-{i}-after')
  deltas={k:after['thermal_counters'][k]-v for k,v in before['thermal_counters'].items() if k.endswith(('_count','_total_time_ms'))}
  assert deltas and all(v>=0 for v in deltas.values()) and not after['read_errors'],'thermal counters unavailable/reset'
  comparisons=compare(i,coin)
  assert all(r['status']=='Ok' for c in comparisons for r in c['records'].values())
  pair=dict(pair=i,coin=coin,order=order,valid=valid,throttled=any(v>0 for v in deltas.values()),thermal_counter_deltas=deltas,comparisons=comparisons)
  pairs.append(pair);write(O/'pairs.json',pairs);print('PAIR',i,'VALID',valid,'THROTTLED',pair['throttled'],flush=True)
  consecutive_invalid=0 if valid else consecutive_invalid+1
  if consecutive_invalid>=3:
   stop_reason='three consecutive invalid pairs';break
except BaseException as e:error=repr(e)
finally:
 end=time.time()
 own=json.loads((R/'window-start.json').read_text())
 cleanup=dict(measurement_end=end,removed=False)
 if MARKER.exists() and json.loads(MARKER.read_text())==own:
  MARKER.unlink();cleanup.update(removed=True,marker_removal_time=time.time())
 write(R/'measurement-marker-removal.json',cleanup)
 def stats(v):
  s=sorted(v)
  def quant(q):
   pos=(len(s)-1)*q;lo=int(pos);hi=min(lo+1,len(s)-1);return s[lo]+(s[hi]-s[lo])*(pos-lo)
  return dict(n=len(v),median=statistics.median(v),p10=quant(.1),p90=quant(.9),seconds=v) if v else dict(n=0)
 timing=[]
 for f in ['transfer','withdrawal']:
  groups={}
  for name,selection in [('all',pairs),('valid_unthrottled',[p for p in pairs if p['valid'] and not p['throttled']]),('valid_throttled',[p for p in pairs if p['valid'] and p['throttled']]),('invalid',[p for p in pairs if not p['valid']])]:
   s={w:stats([c['records'][w]['seconds'] for p in selection for c in p['comparisons'] if c['fixture']==f]) for w in BIN}
   ratio=s['candidate']['median']/s['control']['median'] if s['candidate']['n'] else None
   groups[name]=dict(statistics=s,ratio_candidate_control=ratio)
  valid=len([p for p in pairs if p['valid'] and not p['throttled']])>=PLANNED
  selected=groups['valid_unthrottled'];passed=valid and selected['statistics']['candidate']['median']<15 and selected['ratio_candidate_control']<=1.10
  timing.append(dict(fixture=f,groups=groups,enough_unthrottled=valid,verdict='PASS' if passed else ('FAIL' if valid else 'UNDECIDED')))
 write(O/'comparison.json',dict(start=start,end=end,stop_reason=stop_reason,planned_pairs=PLANNED,completed_pairs=len(pairs),valid_pairs=sum(p['valid'] for p in pairs),invalid_pairs=sum(not p['valid'] for p in pairs),valid_unthrottled_pairs=sum(p['valid'] and not p['throttled'] for p in pairs),unthrottled_pairs=sum(not p['throttled'] for p in pairs),throttled_pairs=sum(p['throttled'] for p in pairs),minimum_unthrottled_pairs=MIN_UNTHROTTLED,error=error,timing=timing,quantiles='linear interpolation inclusive endpoints',passed=error is None and len(pairs)==PLANNED and all(t['verdict']=='PASS' for t in timing),revisions=REV))
if error:raise SystemExit(error)
