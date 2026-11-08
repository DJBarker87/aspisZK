"""Transition the SAME pinned workspace to the import-repaired source revision.
Old objects/sources/freezes remain immutable. Reuse by symlink; rebuild only
changed imports and their dependency descendants. No cold package build.
"""
import pathlib,json,sys,hashlib,re,lzma
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');x=json.load(sys.stdin);old=json.load(open(V/'PLAN.json'));assert old['revision']=='9a38706526c45bc0fac071869458400a07aaaba7'
(V/'PLAN-precanonical.json').write_text(json.dumps(old));(V/'J-precanonical.json').write_bytes((V/'J.json').read_bytes())
S=V/'sources-canonical';O=V/'objects-canonical';S.mkdir(exist_ok=True);O.mkdir(exist_ok=True)
for p in (V/'sources').glob('*.lean'):
 q=S/p.name
 if p.stem in x['changed']:
  text=x['changed'][p.stem];strip=lambda z:'\n'.join(l for l in z.splitlines() if not l.startswith('import '));assert strip(text)==strip(p.read_text());q.write_text(text)
 elif not q.exists():q.symlink_to(p)
plan=json.loads(json.dumps(old));plan['revision']=x['revision'];plan['base_revision']=old['revision']
for m,s in x['changed'].items():
 assert m in plan['rebuild'];plan['rebuild'][m].update(source_origin=x['revision']+':lean/'+m+'.lean',source_sha256=hashlib.sha256(s.encode()).hexdigest(),imports=re.findall(r'^import (\S+)',s,re.M))
affected=set(x['changed']);deps={m:r['imports'] for m,r in plan['rebuild'].items()};deps.update({m:ds for m,ds in old.get('actual_cached_imports',{}).items() if m not in deps and m in old['used']})
while True:
 more={m for m,ds in deps.items() if any(d in affected for d in ds)}-affected
 if not more:break
 affected|=more
assert affected<=set(plan['rebuild']),('affected cache without source pin',sorted(affected-set(plan['rebuild'])))
for p in (V/'objects-resolved').rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(V/'objects-resolved');m=str(rel).split('.olean')[0].removesuffix('.ilean').removesuffix('.ir').replace('/','.')
 if m in affected:continue
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p)
order=[];seen=set();active=set()
def visit(m):
 if m in seen:return
 assert m not in active,('cycle',m);active.add(m)
 for d in deps.get(m,[]):visit(d)
 if m in plan['rebuild']:order.append(m)
 active.remove(m);seen.add(m)
for m in old['order']:visit(m)
plan['order']=order;plan['import_repair_affected']=sorted(affected);(V/'PLAN.json').write_text(json.dumps(plan,indent=2))
env=json.load(open(V/'J.json'));env['LEAN_PATH']=str(O);(V/'J.json').write_text(json.dumps(env))
(V/'evidence/IMPORT_REPLAY_PLAN.json').write_text(json.dumps(dict(revision=x['revision'],affected=sorted(affected),changed=list(x['changed']),declarations_unchanged=True),indent=2))
print(json.dumps(dict(revision=x['revision'],changed=len(x['changed']),affected=len(affected))))
