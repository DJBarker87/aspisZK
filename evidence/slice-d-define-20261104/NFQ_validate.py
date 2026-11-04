#!/usr/bin/env python3
"""Additive, read-only checks on D; does not change NDT/NFK admission."""
import collections, hashlib, json, lzma, pathlib
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
def check(d,c):
 l=json.loads(lzma.open(R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read())
 s=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())
 ds=d['slices']['D']; by={r['row']:r for r in l['rows']}; qs=set(s['slices']['Q']['functions'])|set(s['slices']['S']['functions'])
 assert d['frozen_revision']==l['frozen_revision'];assert len(by)==587
 graph=collections.defaultdict(set)
 for r in by.values():graph[r['function']].update(r['canonical_callees'])
 def closure(roots):
  visit=set(roots);todo=list(visit)
  while todo:
   f=todo.pop()
   for callee in graph[f]:
    if callee in graph and callee not in visit:visit.add(callee);todo.append(callee)
  return visit
 for spec in s['slices'].values():assert closure(spec['roots'])==set(spec['functions'])
 seen=closure(ds['roots'])
 expected=seen-qs;assert set(ds['functions'])==expected;assert not expected&qs
 assert set(ds['inventory_rows'])=={r['row'] for r in by.values() if r['function'] in expected}
 assert set(ds['internal_edges'])=={r['function']+' -> '+x for r in by.values() if r['function'] in expected for x in r['canonical_callees'] if x in expected}
 assert len(c['rows'])==587 and {r['row'] for r in c['rows']}==set(by)
 for row in c['rows']:
  r=by[row['row']];assert row['function']==r['function'] and row['status']==r['composed_status']
  membership=[x for x in ['Q','S'] if r['function'] in s['slices'][x]['functions']]+(['D'] if r['function'] in expected else [])
  assert row['slices']==membership
  path=row['frozen_call_path']
  if path:
   assert path[0] in ds['roots'] and path[-1]==r['function']
   ix={r['function']:r for r in by.values() if r['transaction']==row['transaction']}
   assert all(b in ix[a]['canonical_callees'] for a,b in zip(path,path[1:]))
  gp=row['canonical_union_path']
  if gp:assert gp[0] in ds['roots'] and gp[-1]==r['function'] and all(b in graph[a] for a,b in zip(gp,gp[1:]))
  if not membership:assert row['reason']
 for p,h in c['inputs'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h
 return True
if __name__=='__main__':
 import copy
 d=json.loads((E/'NFQ_SLICE_D.json').read_text());c=json.loads((E/'NFQ_COVERAGE.json').read_text());assert check(d,c)
 mutations=[]
 for name,alter in [('missing function',lambda d,c:d['slices']['D']['functions'].pop()),('extra function',lambda d,c:d['slices']['D']['functions'].append('invented')),('missing edge',lambda d,c:d['slices']['D']['internal_edges'].pop()),('status promotion',lambda d,c:c['rows'][0].update(status='INVENTED')),('membership promotion',lambda d,c:next(r for r in c['rows'] if not r['slices'])['slices'].append('D'))]:
  a,b=copy.deepcopy(d),copy.deepcopy(c);alter(a,b)
  try:check(a,b)
  except AssertionError:mutations.append(dict(name=name,rejected=True))
  else:raise AssertionError(name)
 print(json.dumps(dict(valid=True,mutation_controls=mutations,counts=c['counts']),indent=2))
