"""One lead-allocated exact v8-r3 DATA action using the reviewed bounded collector."""
from pathlib import Path
import datetime,hashlib,json,os,resource,runpy,subprocess,sys,time
E=Path(__file__).resolve().parent
L=json.loads((E/'criteria-ledger.json').read_bytes())
P=Path(L['helper_path'])
assert hashlib.sha256(P.read_bytes()).hexdigest()==L['helper_sha256']
N=runpy.run_path(str(P),run_name='lead_allocated_source')
G=N['future_precharge'].__globals__
# This binding is this committed lead allocation, not untrusted remote DATA.
assert G['FUTURE_ALLOCATION'] is None and L['main_allocated']==1
G['FUTURE_ALLOCATION']=dict(main=1,criteria_sha256=hashlib.sha256((E/'criteria-ledger.json').read_bytes()).hexdigest())
G['CAPTURE']=Path(L['capture'])  # fixed fresh v8 leaf from this trusted committed lead allocation
with (E/'attempt-consumed.json').open('x') as f:
 json.dump(dict(main_allocation_spent=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),formal_calls=0),f);f.flush();os.fsync(f.fileno())
start=time.monotonic();child=None;receipt=None;errors=[]
def write(name,value):
 with (G['CAPTURE']/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
try:
 argv=N['future_precharge'](E/'criteria-ledger.json')
 assert argv==['python3','-B','tools/prover-rw-20261023/final-native-gate/prospective-data-v8-r3/FinalNativeGate-data-transport.py']
 with (G['CAPTURE']/'caller.stdout').open('xb') as out,(G['CAPTURE']/'caller.stderr').open('xb') as err:
  child=subprocess.Popen(argv,stdout=out,stderr=err,start_new_session=True)
  receipt=N['collect_owned'](child,lambda:sum((G['CAPTURE']/x).stat().st_size for x in ('caller.stdout','caller.stderr')),lambda r:write('collector-receipt.json',r))
  # Keep ownership if finite cleanup could not reap; never manufacture completion.
  if not receipt['reaped']:
   while child.poll() is None:time.sleep(.05)
   receipt['exit']=child.wait();receipt['reaped']=True
   receipt['errors'].append('late actual reap after initial cleanup uncertainty')
except BaseException as exc:errors.append(repr(exc))
finally:
 if child is not None and child.poll() is None:
  # No external reaper exists. Retain this owner until the exact Popen exits.
  while child.poll() is None:time.sleep(.05)
  child.wait()
 u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
 summary=dict(capture=str(G['CAPTURE']),transport_exit=None if child is None else child.returncode,
  observer=receipt,errors=errors,wall_seconds=time.monotonic()-start,self_peak_rss_bytes=u.ru_maxrss,
  serial_reaped_child_peak_rss_bytes=c.ru_maxrss,self_swap_counter=u.ru_nswap,child_swap_counter=c.ru_nswap,
  child_rusage_scope='includes owned metadata ps commands, not attributed only to SSH',
  main_allocation_spent=1,conditional_status_calls=0,formal_calls=0,axioms='N/A DATA',targets_established=False)
 with (E/'caller-result.json').open('x') as f:json.dump(summary,f,indent=2);f.write('\n')
 print(json.dumps({k:summary[k] for k in ('capture','transport_exit','errors','wall_seconds','self_peak_rss_bytes','main_allocation_spent')}))
if errors:raise SystemExit(1)
