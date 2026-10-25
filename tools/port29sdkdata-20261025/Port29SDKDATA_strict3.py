#!/usr/bin/env python3
"""One additionally allocated local core-only diagnostic, with focused immutable inputs."""
import collections, hashlib, json, os, re, signal, sqlite3, stat as st, subprocess, sys, time, uuid
from pathlib import Path
from Port29SDKDATA_diagnostic import E,T,OLD,CURRENT,SYS,pin,write,stat
REV='904745b496c1eb84871aacd83b8f9d42f0762613'
NEW=Path('/private/tmp/s126-sdk-current-incremental-release-20261024-v1')
SRC=T/'Port29SDKDATA_Strict-v3.lean'
PREP=E/'Port29SDKDATA_Strict-v3-preparation.json'
REC=E/'Port29SDKDATA_diagnostic-3-receipt.json'
def blob(p,rev=REV):return subprocess.check_output(['git','show',rev+':'+p])
def obj(p,rev=REV):return json.loads(blob(p,rev))
def safe(p):
 p=Path(os.path.abspath(p))
 # /tmp is the system alias /private/tmp; no payload symlink traversal allowed.
 if str(p).startswith('/tmp/'):p=Path('/private'+str(p))
 for q in [p,*p.parents]:
  if q.is_symlink():raise ValueError('symlink, target NOT read: '+str(q))
 if not p.is_file():raise ValueError('missing regular file: '+str(p))
 return p

def prepare():
 assert not PREP.exists() and not REC.exists()
 out=Path('/private/tmp/Port29SDKDATA-Strict-v3-'+uuid.uuid4().hex);out.mkdir(mode=0o700)
 prior=json.loads((E/'Port29SDKDATA_diagnostic-2-preparation.json').read_text());prev=Path(prior['directory'])
 audit=json.loads((E/'Port29SDKDATA_final-audit.json').read_text())
 can=obj('evidence/port18coherence-20261024/canonical-manifest.json')
 manifest=obj('evidence/port18coherence-20261024/manifest.json')
 cb=blob('evidence/port18coherence-20261024/canonical-manifest.json')
 assert hashlib.sha256(cb).hexdigest()==manifest['canonical_manifest_sha256']
 rel=obj('evidence/port18coherence-20261024/transport-manifest.json')
 nm=json.loads((NEW/'manifest.json').read_text());assert pin(NEW/'manifest.json')['sha256']=='49c56b6cfa3ace9d747c9616bfbaea48c39823089adb2eb0bfaacc7cec1e0e83'
 # Immutable publication manifest must match the actual release manifest byte for byte.
 rp='docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-current-incremental-20261024/release-manifest.json'
 assert blob(rp,'103484b3c83bd0115deeb5e5c53bd8521c6d1a20')==(NEW/'manifest.json').read_bytes()
 fresh={};states={};gate=[];index=[];comp=[]
 def add(p,expected=None):
  p=safe(p);key=str(p)
  if key not in fresh:
   x=pin(p)
   if expected:
    assert x['sha256']==expected['sha256'] and x['bytes']==expected['bytes'],key
   fresh[key]=x;states[key]=dict(path=key,pre_stat=stat(p))
  elif expected:assert fresh[key]['sha256']==expected['sha256'] and fresh[key]['bytes']==expected['bytes']
  return key
 def parts(p,expected=None):
  p=add(p,expected)
  for suffix in ['.server','.private']:
   q=Path(p+suffix)
   if q.exists() or q.is_symlink():add(q)
  return p
 # Worklists are reused, but relevant payload bytes are freshly hashed, not the full old audit.
 for file in ['Port29SDKDATA_compare.tsv','Port29SDKDATA_extra-compare.tsv']:
  for line in (prev/file).read_text().splitlines():
   tag,p,q,*names=line.split('\t');comp.append([tag,parts(p),parts(q),*names])
 transports=json.loads(Path(audit['external_transport_manifest']['path']).read_text())['transports']
 assert len(transports)==194
 for r in transports:
  comp.append(['source-readback:'+str(r['part']),parts(r['source']),add(r['path'],r),*r['names']])
 # Inspect full closed checked stage objects, not merely their selected-name manifests.
 for n,attempt in [('CheckedDomain','022'),('CheckedPrepare','023'),('CheckedDriver','025'),('CheckedAccounting','026'),('CheckedAudit','028')]:
  m='Port18COHERENCE_'+n;r=obj(f'evidence/port18coherence-20261024/lean-{attempt}/receipt.json')
  p=Path('/tmp/port18coherence-local-objects')/(m+'.olean')
  p=parts(p,dict(sha256=r['object_sha256'],bytes=p.stat().st_size));index.append(['PORT18-CHECKED','904745b496-checked',m,p])
 for n,attempt in [('Prepare','017'),('Driver','018'),('Accounting','020'),('Effects','022'),('Audit','025')]:
  m='Port17RELEASE_'+n;r=obj(f'evidence/port17release-20261024/lean-{attempt}/receipt.json')
  p=safe(Path('/tmp/port17release-local-objects')/(m+'.olean'))
  z=parts(p,dict(sha256=r['object_sha256'],bytes=p.stat().st_size));index.append(['PORT17-CLOSED','904745b496',m,z])
 missing=json.loads((E/'Port29SDKDATA_final-gaps.json').read_text())['combined_raw_gaps']
 needed={r['port18_manifest_origin'] for r in missing if r['port18_manifest_origin']}
 for r in rel['snapshots']:
  if r['side']+':'+r['module'] in needed:
   p=add(r['path'],r);index.append(['PORT18-RAW',r['side'],r['module'],p])
 # Actual full original part candidates from immutable original_objects, only named local roots.
 for r in can['modules']:
  if r['side']+':'+r['module'] not in needed:continue
  for f in r['original_objects']:
   p=Path('/tmp/port17release-local-dependencies')/Path(f['path']).name if '/' not in r['module'] else None
   # Use exact retained_view when recorded, otherwise module-relative allowed root.
   if 'retained_view' in f:p=Path(f['retained_view'])
   else:
    base=Path('/tmp/port17release-local-dependencies')/(r['module'].replace('.','/')+'.olean')
    tail=f['path'].split('.olean',1)
    p=Path(str(base)+(tail[1] if len(tail)>1 else ''))
   if not str(p).endswith(('.olean','.olean.server','.olean.private')):continue
   try:
    z=add(p,f);gate.append(dict(module=r['module'],path=str(p),status='hash-pinned regular full part',pin=fresh[z]))
    if z.endswith('.olean'):index.append(['PORT17-FULL',r['side'],r['module'],z])
   except (ValueError,AssertionError) as ex:gate.append(dict(module=r['module'],path=str(p),status='UNAVAILABLE: '+str(ex)))
 # Other 37 map to generated S8 types/funs and historical library helpers. No target dereference.
 for m in ['S8OwnedP6.Types','S8OwnedP6.Funs','Mathlib.Data.Bool.Basic','Mathlib.Data.List.Defs','Init.Data.Bool','Init.Data.List.Lemmas']:
  p=Path('/tmp/port17release-local-dependencies')/(m.replace('.','/')+'.olean')
  try:
   # Require an immutable matching object pin, not a new invented hash gate.
   candidates=[f for r in can['modules'] if r['module']==m for f in r['original_objects'] if f['path'].endswith('.olean')]
   safe(p)
   if not candidates:raise ValueError('no immutable full-object pin')
   z=parts(p,candidates[0]);index.append(['PORT17-FULL','904745b496',m,z]);gate.append(dict(module=m,path=str(p),status='hash-pinned regular full parts'))
  except (ValueError,AssertionError) as ex:gate.append(dict(module=m,path=str(p),status='UNAVAILABLE: '+str(ex)))
 # ALL fragments are additions, never replacements. New 141 are indexed, all files preflighted.
 for f in nm['files']:
  p=add(NEW/f['relative'],f)
  if f['relative'].startswith('transport/'):
   m=f['relative'][10:-6].replace('/','.');index.append(['CURRENT-INCREMENTAL','103484b3c83b',m,p])
 assert sum(r[0]=='CURRENT-INCREMENTAL' for r in index)==141
 # Combined duplicates: preserve distinct paths for same-label fragments, use recorded name inventories.
 locations=collections.defaultdict(list)
 for m,p in json.loads((NEW/'audit-input.json').read_text())['transport']:
  locations[m].append(p)
 byname=collections.defaultdict(set)
 # Old final graph supplies names and precise baseline paths; new release supplies fragment names.
 gp=next(x for x in audit['external_outputs'] if x['path'].endswith('final-cross-origin-edges.jsonl'))
 with Path(gp['path']).open() as f:
  for line in f:
   r=json.loads(line)
   if r['side']=='CURRENT':byname[r['name']].add(str(CURRENT/'transport'/(r['module'].replace('.','/')+'.olean')))
 with (NEW/'constants-incremental.jsonl').open() as f:
  for line in f:
   r=json.loads(line);byname[r['name']].add(str(NEW/'transport'/(r['module'].replace('.','/')+'.olean')))
 import itertools
 duplicates={}
 for n,paths in byname.items():
  for a,b in itertools.combinations(sorted(paths),2):duplicates.setdefault((a,b),set()).add(n)
 for (a,b),names in duplicates.items():comp.append(['current-combined-duplicate',add(a),add(b),*sorted(names)])
 # Preflight source and exact inputs for readback comparisons, and retained 564052-row index.
 for p in [SRC,Path(__file__),T/'Port29SDKDATA_strict3_worklist.py',T/'Port29SDKDATA_diagnostic.py',NEW/'manifest.json',NEW/'audit-input.json',NEW/'input.json',NEW/'constants-incremental.jsonl',E/'Port29SDKDATA_final-audit.json',E/'Port29SDKDATA_final-gaps.json']:
  add(p)
 rules=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad')
 for n in ['local-lean.txt','r1p-common.txt','s2-common.txt']:add(rules/n)
 for n in ['Expr.lean','Declaration.lean','Environment.lean','Data/KVMap.lean']:add(SYS/'src/lean/Lean'/n)
 for n in ['Init/Prelude.lean','Init/Meta/Defs.lean']:add(SYS/'src/lean'/n)
 for r in prior['runtime']:add(r['path'],r)
 # Reuse ALL old input byte pins with fresh safe regular-file stat continuity.
 # This allows bounded old-index extraction requests, never another full scan/rehash.
 reused=json.loads((prev/'Port29SDKDATA_input-stat-baseline.json').read_text())
 for r in reused:
  p=safe(r['path']);assert stat(p)==r['pre_stat'],str(p)
  if r['path'] not in states:states[r['path']]=dict(path=r['path'],pre_stat=stat(p),byte_pin_reused=r['sha256'])
 write(out/'Port29SDKDATA_reused-input-pins.json',reused)
 # Retained sqlite byte identity reused from preceding audit; new stat continuity, no full rehash.
 dbpin=next(x for x in audit['external_outputs'] if x['path'].endswith('.sqlite'))
 safe(dbpin['path']);states[dbpin['path']]=dict(path=dbpin['path'],pre_stat=stat(dbpin['path']))
 (out/'Port29SDKDATA_index.tsv').write_text(''.join('\t'.join(r)+'\n' for r in index))
 (out/'Port29SDKDATA_compare.tsv').write_text(''.join('\t'.join(r)+'\n' for r in comp))
 (out/'Port29SDKDATA_export.tsv').write_text('')
 for n in ['Port29SDKDATA_index.tsv','Port29SDKDATA_compare.tsv']:add(out/n)
 x=dict(schema='Port29SDKDATA-Strict-v3-preflight',directory=str(out),source=pin(SRC),inputs=list(fresh.values()),states=list(states.values()),
  closed_object_gates=gate,worklists=dict(index_modules=len(index),comparisons=sum(len(r)-3 for r in comp),comparison_batches=len(comp)),
  prior_sqlite=dbpin,reused_input_pins=pin(out/'Port29SDKDATA_reused-input-pins.json'),previous_audit=pin(E/'Port29SDKDATA_final-audit.json'),
  ownership='Explicit user release authority for named closed roots and exact manifest raw paths. Regular files checked without symlink traversal; immutable hash pin before use; no live donor mutation. no-writer check repeated under local lock.',
  budget=dict(previous_diagnostics=2,additional_allocation=1,global_before=351,global_after=352,remaining=16,unassigned=4,reserved_consumers=5,former_port24=7),
  raw_release_manifest=pin(NEW/'manifest.json'),new_release_report_revision='103484b3c83bd0115deeb5e5c53bd8521c6d1a20',
  new_axioms='N/A: data only',known_symlink_policy='No payload symlinks followed; links remain unavailable even if targets exist.')
 write(PREP,x);print(json.dumps(dict(directory=str(out),worklists=x['worklists'],gates=gate),indent=2))

def run():
 assert not REC.exists();prep=json.loads(PREP.read_text());out=Path(prep['directory'])
 for x in prep['inputs']:assert pin(x['path'])==x,x['path']
 for x in prep['states']:assert stat(x['path'])==x['pre_stat'],x['path']
 lock=Path('/tmp/aspis-local-lean.lock.d');lock.mkdir(mode=0o700)
 try:
  assert not subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True).stdout.strip()
  # Global no-writer evidence is captured before charge, without opening donor payloads.
  proc=subprocess.check_output(['ps','-axo','pid=,ppid=,command='],text=True)
  (out/'Port29SDKDATA_no-writer-processes.txt').write_text(proc)
  # lsof only reports open handles. Every selected local full object must have no writer.
  local=[x['path'] for x in prep['inputs'] if any(k in x['path'] for k in ['port18coherence-local-objects/','port17release-local-objects/','port17release-local-dependencies/','port18coherence-root-snapshots/','port18coherence-candidate-snapshots/'])]
  lf=subprocess.run(['/usr/sbin/lsof','-F','pan','--',*local],capture_output=True,text=True)
  (out/'Port29SDKDATA_no-writer-lsof.txt').write_text(lf.stdout+lf.stderr)
  assert lf.returncode in (0,1)
  assert not any(l.startswith('a') and l[1:] in ['w','u'] for l in lf.stdout.splitlines()),'selected input writer'
  cmd=['/usr/bin/time','-l',str(SYS/'bin/lean'),'-j1','-M4400','-DElab.async=false','-R',str(T),str(SRC)]
  env=os.environ.copy();env.update(LEAN_PATH=str(SYS/'lib/lean'),PORT29_DATA=str(out),PORT29_INTERACTIVE='1')
  r=dict(command=cmd,env={k:env[k] for k in ['LEAN_PATH','PORT29_DATA','PORT29_INTERACTIVE']},source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=pin(SRC),preparation=pin(PREP),launcher=pin(__file__),lean_charged=1,job_cumulative_charged=3,global_actual_after_charge=352,global_ceiling=368,print_axioms='N/A: core-only raw IO diagnostic',status='CHARGED BEFORE LAUNCH',aggregate_child_hard_stop_bytes=8*1024**3,wall_bound_seconds=540)
  write(REC,r);start=time.monotonic();peak=0;pp=0;stop=None
  with (out/'Port29SDKDATA_stdout.log').open('xb') as log,(out/'Port29SDKDATA_time.log').open('xb') as tim,(out/'Port29SDKDATA_processor.log').open('xb') as plog:
   p=subprocess.Popen(cmd,cwd=T,env=env,stdout=log,stderr=tim,start_new_session=True)
   worker=subprocess.Popen([sys.executable,'-B',str(T/'Port29SDKDATA_strict3_worklist.py'),str(out)],stdout=plog,stderr=plog,start_new_session=True)
   while p.poll() is None:
    rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()]
    def descendants(root):
     ids={root}
     while True:
      nxt=ids|{pid for pid,parent,rss in rows if parent in ids}
      if nxt==ids:return ids
      ids=nxt
    ids=descendants(p.pid);ws=descendants(worker.pid)
    prss=sum(rss*1024 for pid,par,rss in rows if pid in ws);pp=max(pp,prss)
    rss=sum(rss*1024 for pid,par,rss in rows if pid in ids|ws);peak=max(peak,rss)
    if rss>=8*1024**3 or prss>=512*1024**2 or time.monotonic()-start>=540 or worker.poll() not in [None,0]:
     stop='aggregate8GiB/processor512MiB/deadline540s/processor failure';os.killpg(p.pid,signal.SIGKILL);break
    time.sleep(.1)
   code=p.wait()
   if worker.poll() is None:os.killpg(worker.pid,signal.SIGKILL)
   wc=worker.wait()
  r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_child_peak_rss_bytes=peak,processor_peak_rss_bytes=pp,processor_exit_status=wc,stopped=stop)
  logs=(out/'Port29SDKDATA_stdout.log').read_text();tim=(out/'Port29SDKDATA_time.log').read_text()
  for suffix,key in [('maximum resident set size','peak_rss_bytes'),('swaps','swaps')]:
   m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[key]=int(m[1]) if m else None
  r['post_stat_unchanged']=all(stat(x['path'])==x['pre_stat'] for x in prep['states'])
  r['post_hash_unchanged']=all(pin(x['path'])==x for x in prep['inputs'])
  r['accepted']=code==0 and wc==0 and 'error:' not in logs and 'PANIC' not in logs and r['post_stat_unchanged'] and r['post_hash_unchanged']
  r['outputs']=[pin(p) for p in sorted(out.rglob('*')) if p.is_file()]
  r['status']='FINISHED; third and final diagnostic; no retry authority'
  REC.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='outputs'}));return 0 if r['accepted'] else 1
 finally:lock.rmdir()
if __name__=='__main__':
 if sys.argv[1]=='prepare':prepare()
 elif sys.argv[1]=='run':sys.exit(run())
