from pathlib import Path
import sys,os,json,subprocess,time,hashlib,statistics
from run import H,run,REVS
mode=sys.argv[1]; O=H/mode;O.mkdir()
cpus=','.join(map(str,sorted(os.sched_getaffinity(0))))
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def snapshot(label):
 x={'utc':time.time(),'label':label,'loadavg':Path('/proc/loadavg').read_text(),'affinity':cpus,'governors':{},'frequencies_khz':{},'cgls':subprocess.run(['systemd-cgls','--user','--no-pager'],text=True,capture_output=True).stdout}
 for p in Path('/sys/devices/system/cpu').glob('cpu[0-9]*/cpufreq'):
  for k,f in [('governors','scaling_governor'),('frequencies_khz','scaling_cur_freq')]:
   try:x[k][p.parent.name]=(p/f).read_text().strip()
   except FileNotFoundError:pass
 write(O/(label+'.json'),x)
def guard(label):
 r=subprocess.run(['python3',str(H/'quiet-preflight.py'),str(O/(label+'-guard.json'))],stdout=subprocess.DEVNULL)
 if r.returncode:raise RuntimeError('foreign capped scope: '+label)
def compare(i,coin):
 rows=[]
 for fixture in ['transfer','withdrawal']:
  files={}
  for name in ['public.bin','proof.bin']:
   a=(O/'control'/f'sample-{i}'/f'{fixture}-{coin}'/name).read_bytes();b=(O/'candidate'/f'sample-{i}'/f'{fixture}-{coin}'/name).read_bytes()
   files[name]={'byte_identical':a==b,'control_sha256':hashlib.sha256(a).hexdigest(),'candidate_sha256':hashlib.sha256(b).hexdigest(),'control_bytes':len(a),'candidate_bytes':len(b)}
  rows.append({'fixture':fixture,'coin':coin,'files':files})
 return rows
snapshot('before');results=[];comparisons=[];error=None
try:
 for i in range(1 if mode=='preflight' else 5):
  coin=99 if mode=='preflight' else 100+i
  order=['control','candidate'] if i%2==0 else ['candidate','control']
  for who in order:
   if mode!='preflight':
    marker=json.loads((H.parent/'QUIET_WINDOW.json').read_text());assert time.time()+60<marker['until'],'window expired or insufficient remaining time'
    guard(f'{who}-{i}-before')
   binary=H/who/'bin/prover_rw_gate';pin=json.loads((H/('pin-'+who+'.json')).read_text());assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin['sha256']
   cmd=['taskset','--cpu-list',cpus,str(binary),str(O/who/f'sample-{i}'),str(coin),'1']
   # Already inside the one capped scope. GNU time supplies per-process receipts.
   with (O/f'{who}-{i}.stdout.log').open('w') as so,(O/f'{who}-{i}.stderr.log').open('w') as se:
    code=subprocess.run(['/usr/bin/time','-v','-o',str(O/f'{who}-{i}.time.log'),*cmd],stdout=so,stderr=se).returncode
   assert code==0,(who,i,code)
   for fixture in ['transfer','withdrawal']:
    row=json.loads((O/who/f'sample-{i}'/f'{fixture}-{coin}'/'result.json').read_text());assert row['status']=='Ok';results.append(dict(side=who,pair=i,order=order,command=cmd,exit_status=code,revision=REVS[who],**row))
   if mode!='preflight':guard(f'{who}-{i}-after')
   write(O/'samples.json',results)
  comparisons+=compare(i,coin);write(O/'proof-comparisons.json',comparisons)
  assert all(f['byte_identical'] for r in comparisons for f in r['files'].values()),'PROOF BYTE MISMATCH'
except BaseException as e:
 error=repr(e)
finally:
 snapshot('after')
 timing=[]
 for fixture in ['transfer','withdrawal']:
  values={w:[r['seconds'] for r in results if r['side']==w and r['fixture']==fixture] for w in ['control','candidate']}
  stats={w:dict(n=len(v),median=statistics.median(v),p10=sorted(v)[0] if len(v)==1 else statistics.quantiles(v,n=10,method='inclusive')[0],p90=sorted(v)[0] if len(v)==1 else statistics.quantiles(v,n=10,method='inclusive')[8]) for w,v in values.items() if v}
  ratio=stats['candidate']['median']/stats['control']['median'] if len(stats)==2 else None
  timing.append(dict(fixture=fixture,seconds=values,statistics=stats,ratio=ratio,passed=bool(ratio is not None and stats['candidate']['median']<15 and ratio<=1.10)))
 write(O/'comparison.json',dict(mode=mode,error=error,timing=timing,comparisons=comparisons,samples=results,quantiles='linear interpolation, inclusive sample endpoints',completed_pairs=len(comparisons)//2,passed=error is None and len(comparisons)==(2 if mode=='preflight' else 10) and all(t['passed'] for t in timing),scope='Fixture timing only; target not yet established'))
if error:raise SystemExit(error)
