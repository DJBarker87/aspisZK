"""Apply actual retained object import headers; change replay order only."""
import pathlib,json,re
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';p=V/'PLAN.json';plan=json.load(open(p));headers=[json.loads(l) for l in (E/'out-56521.log').read_text().splitlines() if l.startswith('{') and '"imports"' in l]
by_path={v['path']:m for m,v in plan['used'].items() if v.get('path')};meta={pathlib.Path(h['path']).stem:h['imports'] for h in headers};assert len(meta)>23
(V/'CACHE_IMPORTS.json').write_text(json.dumps(meta,indent=2));original=plan['order'];seen=set();active=set();order=[]
def visit(m):
 if m in seen:return
 assert m not in active,('cycle',m);active.add(m)
 deps=plan['rebuild'][m]['imports'] if m in plan['rebuild'] else meta.get(m)
 if deps is None:
  if m in plan['rebuild']:deps=plan['rebuild'][m]['imports']
  elif plan['used'].get(m,{}).get('source'):deps=re.findall(r'^import\s+(\S+)',pathlib.Path(plan['used'][m]['source']).read_text(),re.M)
  else:deps=[]
 for d in deps:visit(d)
 if m in plan['rebuild']:order.append(m)
 seen.add(m);active.remove(m)
for m in original:visit(m)
assert set(order)==set(original)
record=dict(changed='dependency order only; no source or statement change',old_order=original,new_order=order,object_headers=meta)
assert order.index('PV_W5_MallocOwned')<order.index('PV_W5_F32Specification')
(E/'ORDER_REPAIR.json').write_text(json.dumps(record,indent=2));plan['order']=order;plan['actual_cached_imports']=meta;p.write_text(json.dumps(plan,indent=2));print('MallocOwned',order.index('PV_W5_MallocOwned'),'F32Specification',order.index('PV_W5_F32Specification'));assert order.index('PV_W5_MallocOwned')<order.index('PV_W5_F32Specification')
