"""Text/data preflight only. No Lean CLI; finite actual-Name origin selection."""
import json,sqlite3,pathlib,subprocess,hashlib,stat,time,resource
T=pathlib.Path(__file__).resolve().parent; E=T.parents[1]/'evidence/port32consumer-20261025'
OUT=pathlib.Path('/private/tmp/Port32CONSUMER-20261025');OUT.mkdir(exist_ok=True,mode=0o700)
def git(p,rev='HEAD'):return subprocess.check_output(['git','show',rev+':'+p])
def key(x):return json.dumps(x,separators=(',',':'),ensure_ascii=False)
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def state(p):
 s=pathlib.Path(p).lstat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_mode,s.st_uid,s.st_nlink]
def safe(p):
 p=pathlib.Path(p)
 for a in [p,*p.parents]:assert not a.is_symlink(),str(a)
 assert stat.S_ISREG(p.stat().st_mode) and p.stat().st_uid==501,str(p)
 return p
start=time.monotonic()
audit=json.loads(git('evidence/port31data-20261025/Port31DATA_audit355.json'));pre=json.loads(git('evidence/port31data-20261025/Port31DATA_preflight-355.json'))
plan=json.loads(git('evidence/port31data-20261025/Port31DATA_next-inputs355.json'))
assert audit['accepted_data']
dbp=pathlib.Path('/private/tmp/Port31DATA-355-20261025/Port31DATA_inventory355.sqlite')
assert pin(safe(dbp))==next(x for x in audit['outputs'] if x['path']==str(dbp))
db=sqlite3.connect('file:'+str(dbp)+'?mode=ro',uri=True)
def records(n):
 return [dict(origin=o,kind=k,unsafe=u,partial=p,value=v,info=json.loads(i)) for o,k,u,p,v,i in db.execute('select origin,kind,unsafe,partial,value,info from constant where name=?',(n,))]
standard={key(['str',['anon'],'propext']),key(['str',['str',['anon'],'Classical'],'choice']),key(['str',['str',['anon'],'Quot'],'sound'])}
# Declared policy: full safe body, whole current computation context, newer released
# source first; original ROOT where current is absent. Core private full bodies first.
def rank(r):
 o=r['origin']
 if o.startswith('CORE:'):return (0,-int(o.rsplit('part',1)[1]),o)
 for i,prefix in enumerate(['BOOL:','S8:','CURRENT:SELECTED:','CURRENT:INCREMENTAL:','CURRENT:BASE:','ROOT87:','PRIOR194:','PRIOR256:']):
  if o.startswith(prefix):return (i+1,0,o)
 raise AssertionError(o)
def eligible(n,r):return not r['unsafe'] and not r['partial'] and (r['kind']!='axiom' or n in standard) and (r['kind'] not in ['definition','theorem','opaque'] or r['value'])
# Shim is new source, never a historical identity; actual old applications are replayed.
def name(s):
 n=['anon']
 for a in s.split('.'):n=['str',n,a]
 return n
roots=[name(s) for s in ['AspisR1.S2W_D189Consolidation.accepted_run','AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace','AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts']]
shim=key(name('Bool.eq_true_of_not_eq_false')); chosen={};todo=[key(n) for n in roots];gaps=[]
while todo:
 n=todo.pop()
 if n in chosen or n==shim:continue
 rs=sorted([r for r in records(n) if eligible(n,r)],key=rank)
 if not rs:gaps.append(dict(name=json.loads(n),variants=records(n)));continue
 r=rs[0]
 todo.extend(key(d) for d in r['info']['dependencies'] if key(d) not in chosen)
 r['info'].pop('dependencies');chosen[n]=r
assert not gaps,[(g['name'],[(v['origin'],v['kind']) for v in g['variants']]) for g in gaps[:5]]
# Full group header/constructor membership and recursor parent edges already occur
# in 355 dependencies; independently require exactly matching selected group headers.
group_checks=0
for n,r in chosen.items():
 c=r['info'];m=c['metadata']
 if r['kind']=='inductive':
  for a in m[0]:
   q=chosen[key(a)]['info'];assert q['kind']=='inductive' and q['metadata'][0]==m[0] and q['levels']==c['levels']
  for ctor in m[1]:assert chosen[key(ctor)]['info']['metadata'][0]==c['name']
  group_checks+=1
 elif r['kind'] in ['definition','theorem','opaque']:
  members=m[0] if r['kind']=='definition' else m
  for a in members:assert key(a) in chosen,(c['display'],a)
origins=sorted({r['origin'] for r in chosen.values()});oi={s:i for i,s in enumerate(origins)}
selection=dict(origins=origins,roots=roots,choices=[[json.loads(n),oi[r['origin']]] for n,r in sorted(chosen.items())])
sp=OUT/'Port32CONSUMER_selection.json';sp.write_text(key(selection)+'\n')
# Materialize only needed raw source parts, using already strict-readback exports
# for own/Core inputs. Historical groups never read a .server/.private alone.
exports={r['origin']:r['path'] for r in audit['exports']['observed']};states={r['path']:r for r in pre['states']}
groups=[];pins=[];continuity=[]
for g in plan['groups']:
 needed=[g['label']+':part'+str(i) for i in range(len(g['paths'])) if g['label']+':part'+str(i) in oi]
 if not needed:continue
 if g['kind'] in ['CORE','OWN']:
  for o in needed:
   p=exports[o];x=next(x for x in audit['exports']['pins'] if x['path']==p);assert pin(safe(p))==x
   groups.append([o,p]);pins.append(x)
 else:
  assert len(g['paths'])==1
  p=g['paths'][0];assert state(safe(p))==states[p]['stat'],p
  groups.append([g['label']+':part0',p]);continuity.append(dict(path=p,stat=state(p),sha256=states[p].get('byte_pin'),assessment='REUSED355 byte hash; safe/stat continuity, no new identity gate'))
gp=OUT/'Port32CONSUMER_groups.json';gp.write_text(key(groups)+'\n');assert {o for o,p in groups}==set(origins)
assert sum(pathlib.Path(p).stat().st_size for o,p in groups)<512*1024**2
variants=json.loads(git('evidence/port31data-20261025/Port31DATA_variant-map-v2355.json'))
assess=[]
for row in variants['categories']:
 picks=[dict(name=a,origin=chosen[key(a)]['origin'],kind=chosen[key(a)]['kind']) for a in row['actual_names'] if key(a) in chosen]
 assess.append(dict(category=row['category'],presentation_label=row['presentation_label'],selected=picks,assessment='NEW chosen-context ordinary kernel re-pin required; NO historical literal equivalence; all old variants retained in immutable355 provenance'))
(E/'Port32CONSUMER_variant-assessment.json').write_text(json.dumps(assess,indent=2)+'\n')
# Retain the complete before/after and selected source texts from immutable Git.
for row in json.loads(git('evidence/port30join-20261025/source-pins.json')):
 if row['exit']==0:
  b=git(row['path'],row['revision']);assert hashlib.sha256(b).hexdigest()==row['sha256']
# Runtime/tool/source pins are a bounded subset; prior all-core inventory is reused.
sysroot=pathlib.Path(pre['sysroot']);runtime=[]
for x in pre['fresh_pins']:
 if x['path'].startswith(str(sysroot)) and (x['path'].endswith('.dylib') or '/bin/' in x['path'] or '/src/' in x['path'] or pathlib.Path(x['path']).name in ['Lean.olean','Lean.olean.server','Lean.olean.private','Init.olean','Init.olean.server','Init.olean.private']):
  assert pin(safe(x['path']))==x;runtime.append(x)
assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 512*1024**2
r=dict(status='TEXT/DATA PREFLIGHT ONLY; no kernel claim',selection=pin(sp),groups=pin(gp),selected_names=len(chosen),selected_origins=len(origins),raw_bytes=sum(pathlib.Path(p).stat().st_size for o,p in groups),group_checks=group_checks,roots=roots,shim=name('Bool.eq_true_of_not_eq_false'),policy='Full safe body; CORE private before other CORE; BOOL,S8,CURRENT selected/incremental/base,ROOT87,PRIOR194,PRIOR256; lexical tie break. Every conflict is NEW re-pin, not identity',pins=pins+[pin(sp),pin(gp)],states=continuity,runtime=runtime,reused_inventory=pin(dbp),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sysroot=str(sysroot),wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,lean_calls=0,exit_status=0,core_assessment=pre['core_dependency_assessment'],new_identity_gate=False)
(E/'Port32CONSUMER_preflight.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','selected_names','selected_origins','raw_bytes','group_checks','wall_seconds','peak_rss_bytes','lean_calls']}))
