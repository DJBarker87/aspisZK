"""Bounded exact-name SQLite planning, not compilation or logical validation."""
import hashlib,json,pathlib,sqlite3,subprocess,time,resource
T=pathlib.Path(__file__).resolve().parent; E=T.parents[1]/'evidence/port33interface-20261025'
def pin(p):
 p=pathlib.Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def key(x):return json.dumps(x,separators=(',',':'),ensure_ascii=False)
def name(s):
 n=['anon']
 for x in s.split('.'): n=['str',n,x]
 return n
def git(p):return subprocess.check_output(['git','show','b978d1d000:'+p])
start=time.monotonic()
pre=json.loads((E/'Port33INTERFACE_reused-preflight.json').read_text())
db=sqlite3.connect('file:'+pre['reused_inventory']['path']+'?mode=ro',uri=True);db.execute('pragma cache_size=-8192')
targets=[name('AspisR1PublicPreparation.Query31SourceSchedule.'+x) for x in ['queries_success_with_digest_pairs_full','queries_success_pairs_functional_full']]
todo=list(targets);seen=set();rows=[]
while todo:
 n=todo.pop();k=key(n)
 if k in seen:continue
 seen.add(k)
 for o,display,kind,u,p,v,info in db.execute('select origin,display,kind,unsafe,partial,value,info from constant where name=?',(k,)):
  i=json.loads(info); rows.append(dict(name=n,origin=o,display=display,kind=kind,unsafe=u,partial=p,value=v,info=i))
  for dep in i['dependencies']:
   # Exact names from reviewed inventory; bounded local source/group/schedule interface.
   s=key(dep)
   if 'Query31' in s or 'QueriesModel' in s:todo.append(dep)
origins=sorted({r['origin'] for r in rows})
groups=dict(json.loads(pathlib.Path(pre['groups']['path']).read_text()))
plan=json.loads(git('evidence/port31data-20261025/Port31DATA_next-inputs355.json'))
audit=json.loads(git('evidence/port31data-20261025/Port31DATA_audit355.json'))
exports={r['origin']:r['path'] for r in audit['exports']['observed']}
for g in plan['groups']:
 for ix,p in enumerate(g['paths']):
  o=g['label']+':part'+str(ix)
  if o in origins and o not in groups:
   assert g['kind'] not in ['CORE','OWN'] or o in exports
   groups[o]=exports.get(o,p)
files=[]
for ix,o in enumerate(origins):
 p=pathlib.Path(groups[o]);assert str(p).startswith('/private/tmp/') and '.worktrees' not in str(p)
 assert not p.is_symlink();files.append(dict(origin=o,**pin(p),names=[r['name'] for r in rows if r['origin']==o],output=f'/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part{ix}.olean'))
assert sum(x['bytes'] for x in files)<512*1024**2
r=dict(status='DATA plan; no type or proof identity claim',immutable_revision='b978d1d000',targets=targets,rows=rows,files=files,inventory_assessment='355 SQLite SHA reused; exact-name queries only; no inventory rehash/scan',inventory=pre['reused_inventory'],wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,lean_calls=0)
assert r['peak_rss_bytes']<512*1024**2
(E/'Port33INTERFACE_plan.json').write_text(json.dumps(r,indent=2)+'\n')
print(dict(names=len(seen),variants=len(rows),containers=len(files),bytes=sum(x['bytes'] for x in files),rss=r['peak_rss_bytes']))
