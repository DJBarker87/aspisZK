from pathlib import Path
from types import SimpleNamespace
import importlib.util,json,time
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-proof-20261016');spec=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
original=r.verify_snapshot;cache=None
def once(path):
 global cache
 if cache is None:cache=original(path)
 else:
  for p,stat in cache[1].items():
   s=Path(p).stat();assert(s.st_size,s.st_mtime_ns)==stat,('Pinned source/cache changed',p)
 return cache
r.verify_snapshot=once
guard=r.external_lean;events=[]
def observed(own=None):
 active=guard(own)
 if active and (not events or events[-1]['pids']!=active or events[-1]['own_pid']!=own):
  events.append({'utc':time.time(),'pids':active,'own_pid':own});(W/'guard-events.json').write_text(json.dumps(events,indent=2)+'\n');print('EXTERNAL LEAN WAIT/STOP '+str(active),flush=True)
 return active
r.external_lean=observed
for phase in ['base','model','reach']:
 marker=W/('START-'+phase)
 while not marker.exists():time.sleep(.2)
 targets={'base':['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','ExtractedPreparedModel'],'model':['ExtractedTx1Model'],'reach':['ExtractedTx1Reachability']}[phase]
 for attempt in range(1,7):
  manifest=r.staged(W);args=SimpleNamespace(workspace=W,target=targets,group=None,external_snapshot=W/'external-inputs.json',attempt='tx1-'+phase+'-guarded-b'+str(attempt),revision='e5c186ba3bcbbf9a0cc5878077aa8848853a65cc+shared-canonical-a2b07cd9')
  before=len(events);code=r.run(args,manifest)
  record={'exit':code,'target':targets,'attempt':args.attempt,'guard_events_since':events[before:],'pinned_import_hashes_retained_in_memory':True}
  (W/('DONE-'+phase+'-'+str(attempt))).write_text(json.dumps(record)+'\n')
  if not code:(W/('DONE-'+phase)).write_text(json.dumps(record)+'\n');break
  if any(e['own_pid'] is not None for e in events[before:]):
   while observed():time.sleep(.2)
   continue
  retry=W/('RETRY-'+phase+'-'+str(attempt))
  print('WAIT CHANGED SOURCE/RETRY MARKER '+str(retry),flush=True)
  while not retry.exists():time.sleep(.2)
 else:raise SystemExit(code)
