from pathlib import Path
from types import SimpleNamespace
import importlib.util,json,time
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-read-proof-20261018');spec=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
original=r.verify_snapshot;cache=None
def once(path):
 global cache
 if cache is None:
  print('PINNED CLOSURE HASH PREFLIGHT START '+str(time.time()),flush=True);cache=original(path);print('PINNED CLOSURE HASH PREFLIGHT DONE '+str(time.time()),flush=True)
 else:
  for p,stat in cache[1].items():
   s=Path(p).stat();assert(s.st_size,s.st_mtime_ns)==stat,('Pinned source/cache changed',p)
 return cache
r.verify_snapshot=once;guard=r.external_lean;events=[]
def observed(own=None):
 active=guard(own)
 if active and(not events or events[-1]['pids']!=active or events[-1]['own_pid']!=own):
  events.append({'utc':time.time(),'pids':active,'own_pid':own});(W/'guard-events.json').write_text(json.dumps(events,indent=2)+'\n');print('EXTERNAL LEAN WAIT/STOP '+str(active),flush=True)
 return active
r.external_lean=observed
for target in ['ExtractedSourceSemanticSampler','ExtractedSelectedSourceRecords']:
 for attempt in range(1,101):
  args=SimpleNamespace(workspace=W,target=[target],group=None,external_snapshot=W/'external-inputs.json',attempt='source-read-'+target+'-'+str(attempt),revision='a555c852664c80000942f0c911e16719a5493625')
  before=len(events)
  try:code=r.run(args,r.staged(W))
  except TimeoutError:
   print('Shared lock queue bounded45s; next environment acquisition attempt',flush=True);continue
  record={'exit':code,'target':target,'attempt':args.attempt,'guard_events_since':events[before:]};(W/('DONE-source-read-'+target+'-'+str(attempt))).write_text(json.dumps(record)+'\n')
  if not code:(W/('DONE-source-read-'+target)).write_text(json.dumps(record)+'\n');break
  if any(e['own_pid'] is not None for e in events[before:]):
   while observed():time.sleep(.2)
   continue
  marker=W/('RETRY-source-read-'+target+'-'+str(attempt));print('WAIT CHANGED SOURCE '+str(marker),flush=True)
  while not marker.exists():time.sleep(.2)
 else:raise SystemExit(code)
print('ACTUAL SOURCE READ BRIDGES GREEN',flush=True)
