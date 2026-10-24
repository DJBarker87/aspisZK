#!/usr/bin/env python3
"""Exclusive, charged core-only diagnostics. No build, project import or host access."""
import collections, hashlib, itertools, json, os, re, signal, subprocess, sys, time, uuid
from pathlib import Path
T=Path(__file__).resolve().parent
R=T.parents[1]
E=R/'evidence/port29sdkdata-20261025'
OLD=Path('/private/tmp/port28rootexport-20261024-2e053459f91b43c3b4c640d575d607c9')
CURRENT=Path('/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1')
SYS=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0')
def pin(p):
 p=Path(p); h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024**2),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def write(p,x):
 with Path(p).open('x') as f:json.dump(x,f,indent=2);f.write('\n')
def stat(p):
 s=Path(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_mode]
def old_inputs():
 a=json.loads((OLD/'correction-output-audit.json').read_text())
 d=json.loads(Path(a['reused_input_manifest']['path']).read_text())
 return a,d
def prepare():
 a,d=old_inputs(); out=Path('/private/tmp/Port29SDKDATA-diagnostic-'+uuid.uuid4().hex);out.mkdir(mode=0o700)
 rows=[]
 for p in (OLD/'core.tsv').read_text().splitlines():
  m=str(Path(p).relative_to(SYS/'lib/lean'))[:-6].replace('/','.')
  rows.append(['CORE','pinned-4.32',m,p])
 for row in (OLD/'objects.tsv').read_text().splitlines():
  origin,m,p=row.split('\t');rows.append(['ORIGINAL',origin,m,p])
 (out/'Port29SDKDATA_index.tsv').write_text(''.join('\t'.join(x)+'\n' for x in rows))
 groups=collections.defaultdict(set)
 for n,rs in a['duplicate_name_origins'].items():
  for x,y in itertools.combinations(rs,2):groups[('root-duplicate',x['path'],y['path'])].add(n)
 graph_pin=next(x for x in json.loads((E/'Port29SDKDATA_audit.json').read_text())['retained_outputs'] if x['path'].endswith('cross-origin-edges.jsonl'))
 current=collections.defaultdict(set)
 with Path(graph_pin['path']).open() as f:
  for line in f:
   row=json.loads(line)
   if row['side']=='CURRENT':current[row['name']].add(str(CURRENT/'transport'/(row['module'].replace('.','/')+'.olean')))
 for t in a['final_round_transports']:
  for n in t['names']:
   for p in current[n]:groups[('original-current',t['path'],p)].add(n)
 (out/'Port29SDKDATA_compare.tsv').write_text(''.join('\t'.join([*k,*sorted(v)])+'\n' for k,v in sorted(groups.items())))
 (out/'Port29SDKDATA_export.tsv').write_text('')
 prior=json.loads((E/'Port29SDKDATA_audit.json').read_text()); pp=next(x for x in prior['retained_outputs'] if x['path'].endswith('input-pins.json'))
 pins=json.loads(Path(pp['path']).read_text()); observation={x['path']:x for x in pins}
 # Prior verified bytes are reused; stat tokens are NEW observations, not historical identity gates.
 states=[]
 for p,x in sorted(observation.items()):
  s=stat(p);assert s[2]==x['bytes'],p
  states.append(dict(**x,pre_stat=s,hash_assessment='Reused prior pre/post SHA256; new stat continuity check, no repeated 2.8GB hash gate'))
 write(out/'Port29SDKDATA_input-stat-baseline.json',states)
 rules=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad')
 api=[SYS/'src/lean/Lean/Environment.lean',SYS/'src/lean/Lean/Declaration.lean',SYS/'src/lean/Init/System/IO.lean']
 prep=dict(schema='Port29SDKDATA-diagnostic-preparation-v1',directory=str(out),source=pin(T/'Port29SDKDATA_Raw.lean'),
  rules=[pin(rules/n) for n in ['local-lean.txt','r1p-common.txt','s2-common.txt']],api=[pin(p) for p in api],
  runtime=[pin(x['path']) for x in d['runtime']],index_modules=len(rows),core_modules=sum(x[0]=='CORE' for x in rows),
  original_modules=sum(x[0]=='ORIGINAL' for x in rows),comparison_batches=len(groups),
  comparison_entries=sum(map(len,groups.values())),inputs=[pin(p) for p in out.iterdir()],
  previous_input_hash_audit=pin(E/'Port29SDKDATA_audit.json'),lean_invocations=0,
  current_rules='NEW lead-supplied rules; original missing-file history preserved',
  indexing='Every part ConstantInfo/dependency/kind/metadata; full values retained in pinned raw objects; no environment insertion')
 write(E/'Port29SDKDATA_diagnostic-1-preparation.json',prep);print(json.dumps({k:prep[k] for k in ['directory','index_modules','comparison_batches','comparison_entries']}))
def prepare2():
 first=json.loads((E/'Port29SDKDATA_diagnostic-1-preparation.json').read_text())
 out=Path('/private/tmp/Port29SDKDATA-diagnostic-'+uuid.uuid4().hex);out.mkdir(mode=0o700)
 for n in ['Port29SDKDATA_index.tsv','Port29SDKDATA_compare.tsv','Port29SDKDATA_input-stat-baseline.json']:
  (out/n).write_bytes((Path(first['directory'])/n).read_bytes())
 (out/'Port29SDKDATA_export.tsv').write_text('')
 x={**first,'directory':str(out),'source':pin(T/'Port29SDKDATA_Raw.lean'),
  'inputs':[pin(p) for p in out.iterdir()]+[pin(T/'Port29SDKDATA_worklist.py')],
  'runtime':[pin(p['path']) for p in first['runtime']],
  'reason':'Changed source corrects non-Inhabited array access and record layout. Same invocation supplies previously missing extraction artifact through a bounded noncompiler worklist handshake.',
  'failed_source':pin(T/'Port29SDKDATA_Raw-failed-diagnostic1.lean.txt'),
  'processor':pin(T/'Port29SDKDATA_worklist.py')}
 write(E/'Port29SDKDATA_diagnostic-2-preparation.json',x);print(json.dumps({'directory':str(out),'source':x['source']}))
def run(number):
 assert number in [1,2]
 prep=json.loads((E/f'Port29SDKDATA_diagnostic-{number}-preparation.json').read_text());out=Path(prep['directory'])
 assert pin(T/'Port29SDKDATA_Raw.lean')==prep['source']
 for x in prep['inputs']+prep['runtime']+prep['api']+prep['rules']:assert pin(x['path'])==x,x['path']
 baseline=json.loads((out/'Port29SDKDATA_input-stat-baseline.json').read_text())
 for x in baseline:assert stat(x['path'])==x['pre_stat'],x['path']
 assert not (out/'Port29SDKDATA_raw.jsonl').exists()
 lock=Path('/tmp/aspis-local-lean.lock.d');lock.mkdir(mode=0o700)
 receipt=E/f'Port29SDKDATA_diagnostic-{number}-receipt.json'
 try:
  assert not subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True).stdout.strip(),'Other local Lean running'
  lean=SYS/'bin/lean';cmd=['/usr/bin/time','-l',str(lean),'-j1','-M4400','-DElab.async=false','-R',str(T),str(T/'Port29SDKDATA_Raw.lean')]
  env=os.environ.copy();env['LEAN_PATH']=str(SYS/'lib/lean');env['PORT29_DATA']=str(out)
  if number==2:env['PORT29_INTERACTIVE']='1'
  r=dict(schema='Port29SDKDATA-raw-diagnostic-receipt-v1',command=cmd,env={k:env[k] for k in ['LEAN_PATH','PORT29_DATA']+(['PORT29_INTERACTIVE'] if number==2 else [])},
   source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=prep['source'],
   preparation=pin(E/f'Port29SDKDATA_diagnostic-{number}-preparation.json'),launcher=pin(__file__),
   lean_charged=1,job_cumulative_charged=number,global_actual_after_charge=349+number,global_ceiling=368,
   print_axioms='N/A: raw ConstantInfo IO diagnostic; no theorem/check/insertion',
   aggregate_child_hard_stop_bytes=8*1024**3,wall_bound_seconds=540,status='CHARGED before launch')
  write(receipt,r)
  start=time.monotonic();peak=0;stop=None;processor=None;processor_peak=0
  with (out/'Port29SDKDATA_stdout.log').open('xb') as log,(out/'Port29SDKDATA_time.log').open('xb') as tim:
   p=subprocess.Popen(cmd,cwd=T,env=env,stdout=log,stderr=tim,start_new_session=True)
   if number==2:
    proc_log=(out/'Port29SDKDATA_worklist-stdout.log').open('xb')
    proc_time=(out/'Port29SDKDATA_worklist-time.log').open('xb')
    processor=subprocess.Popen(['/usr/bin/time','-l',sys.executable,'-B',str(T/'Port29SDKDATA_worklist.py'),str(out)],stdout=proc_log,stderr=proc_time,start_new_session=True)
   while p.poll() is None:
    rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()];ids={p.pid}
    while True:
     nxt=ids|{pid for pid,ppid,rss in rows if ppid in ids}
     if nxt==ids:break
     ids=nxt
    if processor is not None:
     procs={processor.pid}
     while True:
      nxt=procs|{pid for pid,ppid,rss in rows if ppid in procs}
      if nxt==procs:break
      procs=nxt
     prss=sum(rss*1024 for pid,ppid,rss in rows if pid in procs);processor_peak=max(processor_peak,prss)
     ids.update(procs)
     if prss>=512*1024**2 or processor.poll() not in [None,0]:
      stop='bounded worklist processor failure/512MiB hard stop';os.killpg(p.pid,signal.SIGKILL);break
    rss=sum(rss*1024 for pid,ppid,rss in rows if pid in ids);peak=max(peak,rss)
    if rss>=8*1024**3 or time.monotonic()-start>=540:
     stop='aggregate 8GiB hard stop' if rss>=8*1024**3 else '540s deadline';os.killpg(p.pid,signal.SIGKILL);break
    time.sleep(.1)
   code=p.wait()
   if processor is not None:
    if processor.poll() is None:os.killpg(processor.pid,signal.SIGKILL)
    r['processor_exit_status']=processor.wait();r['processor_aggregate_peak_rss_bytes']=processor_peak
    proc_log.close();proc_time.close()
  r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_child_peak_rss_bytes=peak,stopped=stop)
  text=(out/'Port29SDKDATA_time.log').read_text()
  for suffix,key in [('maximum resident set size','peak_rss_bytes'),('swaps','swaps')]:
   found=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',text,re.M);r[key]=int(found[1]) if found else None
  r['post_stat_unchanged']=all(stat(x['path'])==x['pre_stat'] for x in baseline)
  r['runtime_post_hash_unchanged']=all(pin(x['path'])==x for x in prep['runtime'])
  r['outputs']=[pin(p) for p in sorted(out.iterdir()) if p.name not in {Path(x['path']).name for x in prep['inputs']} and p.is_file()]
  logs=(out/'Port29SDKDATA_stdout.log').read_text()
  r['accepted']=code==0 and 'error:' not in logs and 'PANIC' not in logs and r['post_stat_unchanged'] and r['runtime_post_hash_unchanged']
  r['status']='FINISHED; retained outcome, no unchanged rerun'
  receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));return 0 if r['accepted'] else 1
 finally:lock.rmdir()
if __name__=='__main__':
 if sys.argv[1]=='prepare':prepare()
 elif sys.argv[1]=='prepare2':prepare2()
 else:sys.exit(run(int(sys.argv[1])))
