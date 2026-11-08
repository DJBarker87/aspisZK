"""Stage the pinned merged source and select hash-verified cached providers."""
import pathlib,json,sys,hashlib,lzma,subprocess,re,collections
R=pathlib.Path('/home/dombarker/project-offloads');P=R/'codex-pv-lib-slice-20261107';V=P/'v1-coherence';E=V/'evidence';E.mkdir(exist_ok=True)
x=json.load(sys.stdin);inv=x['inventory'];(V/'INVENTORY.json').write_text(json.dumps(inv))
S=V/'sources';O=V/'objects-resolved';S.mkdir(exist_ok=True);O.mkdir(exist_ok=True)
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
for m,b in x['sources'].items():
 p=S/(m+'.lean');assert not p.exists() or p.read_text()==b;p.write_text(b);assert sha(p)==inv['sources'][m]['sha256']
cs=json.load(open(V/'CACHE_SURVEY.json'))
# Add accepted lane objects that need not have appeared as another module's dependency.
for base in [P,R/'codex-pv-lib-20261107',R/'codex-pv-lib-20261107/lane-A',R/'codex-pv-lib-spec-20261107']:
 for f in list((base/'evidence').glob('receipt-*.json'))+list((base/'lane-B/evidence').glob('receipt-*.json')):
  r=json.load(open(f));m=r.get('target');h=r.get('object_sha256')
  if not r.get('accepted') or not h or not isinstance(m,str):continue
  for d in base.glob('objects*'):
   o=d/(m+'.olean')
   if not o.exists() or sha(o)!=h:continue
   for sd in base.glob('sources*'):
    s=sd/(m+'.lean')
    if s.exists() and sha(s)==r.get('source_sha256'):
     cs.append(dict(module=m,path=str(o),sha256=h,source=str(s),source_sha256=sha(s),authority=str(f)));break
by=collections.defaultdict(list)
for c in cs:by[c['module']].append(c)
# The adopted C19 authority has priority; base and STX complement it read-only.
def priority(c):
 a=c['authority'];
 if c['module'].startswith(('PV_STX2_','PV_W5_','PV_FN_SLICE_')) and 'resolution-49922' in a:return (-1,a)
 return (0 if 'resolution-56254' in a else 1 if 'resolution-44941' in a else 2 if 'resolution-49705' in a else 3 if 'resolution-49922' in a else 4,a)
selected={m:sorted(vs,key=priority)[0] for m,vs in by.items()}
# Resolve source path even when a flattened authority records objects only.
for m,c in selected.items():
 if not c.get('source'):
  same=[v for v in by[m] if v['sha256']==c['sha256'] and v.get('source')]
  if same:c.update(source=same[0]['source'],source_sha256=same[0]['source_sha256'])
missing=[m for m in inv['external_imports'] if m not in selected and m!='Lean'];assert not missing,missing
# Import closure of retained provider sources, with exact authority dependency hashes.
used={};rebuild={};visiting=set();conflicts=[]
metadata=json.load(open(V/'CACHE_IMPORTS.json')) if (V/'CACHE_IMPORTS.json').exists() else {}
rescache={}
def resolution(c):
 p=pathlib.Path(c['authority'])
 if 'resolution-' not in p.name:return None
 if str(p) not in rescache:
  z=json.loads(lzma.decompress(p.read_bytes()));rescache[str(p)]=z.get('modules',z)
 return rescache[str(p)]
def visit(m):
 if m in used or m=='Lean':return
 if m in visiting:raise RuntimeError('cycle '+m)
 visiting.add(m)
 if m in inv['sources']:
  text=(S/(m+'.lean')).read_text();c=None
  if not m.startswith('PV_LIB_'):
   matches=[v for v in by[m] if v.get('source_sha256')==inv['sources'][m]['sha256']]
   if matches:
    c=sorted(matches,key=priority)[0];selected[m]=c
 else:
  c=selected.get(m);assert c,('missing provider',m)
  if not c.get('source'):
   assert m in metadata,('read actual object import headers before staging a source-free provider',m,c['path'])
   for d in metadata[m]:visit(d)
   used[m]=c;visiting.remove(m);return
  text=pathlib.Path(c['source']).read_text()
 deps=re.findall(r'^import\s+(\S+)',text,re.M)
 for d in deps:visit(d)
 if c:
  authority=resolution(c);mismatch=[]
  if authority:
   for d in deps:
    if d=='Lean':continue
    old=authority.get(d,{}).get('sha256');new=used.get(d,{}).get('sha256')
    if d in rebuild or (old and old!=new):mismatch.append(dict(module=d,expected=old,selected=new))
  elif any(d in rebuild for d in deps):mismatch=[dict(module=d) for d in deps if d in rebuild]
  if mismatch:
   conflicts.append(dict(module=m,authority=c['authority'],dependencies=mismatch));rebuild[m]=dict(source_origin=c['source'],source_sha256=c['source_sha256'],imports=deps)
   (S/(m+'.lean')).write_text(text);used[m]=dict(rebuild=True)
  else:used[m]=c
 else:
  rebuild[m]=dict(source_origin='merged revision',source_sha256=inv['sources'][m]['sha256'],imports=deps);used[m]=dict(rebuild=True)
 visiting.remove(m)
for m in inv['order']:visit(m)
# Pinned external package cache closure is already hash-verified by the survey.
for m,c in selected.items():
 if m in rebuild:continue
 o=O/(m.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
 if not o.exists():o.symlink_to(c['path'])
 # Preserve Lean's required companion data, without modifying any source cache.
 for ext in ['.olean.private','.olean.server','.ilean','.ir']:
  src=pathlib.Path(c['path']).with_suffix(ext) if ext in ['.ilean','.ir'] else pathlib.Path(c['path']+ext[len('.olean'):])
  dest=pathlib.Path(str(o).removesuffix('.olean')+ext)
  if src.exists() and not dest.exists():dest.symlink_to(src)
order=[];seen=set()
def sort(m):
 if m in seen:return
 seen.add(m)
 deps=metadata.get(m,rebuild.get(m,{}).get('imports',[]))
 for d in deps:sort(d)
 if m in rebuild:order.append(m)
for m in inv['order']:sort(m)
env=json.load(open(R/'codex-pv-int-20261106/J.json'));env['LEAN_PATH']=str(O);(V/'J.json').write_text(json.dumps(env))
(V/'PLAN.json').write_text(json.dumps(dict(revision=inv['source_revision'],order=order,rebuild=rebuild,used=used,conflicts=conflicts),indent=2))
print(json.dumps(dict(rebuild=len(order),providers=len(used)-len(rebuild),cache_dependency_conflicts=len(conflicts),first=order[:12])))
