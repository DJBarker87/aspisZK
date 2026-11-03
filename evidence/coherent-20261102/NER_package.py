"""Package task-owned scanner output without modifying any source cohort."""
from pathlib import Path
import hashlib,json,lzma
B=Path(__file__).resolve().parent
mods={r['module']:r for r in map(json.loads,(B/'NER_MANIFEST.jsonl').open())}
rows=list(map(json.loads,(B/'NER_SCAN_ROWS.jsonl').open()))
assert set(mods)=={r['module'] for r in rows}
stale={r['module'] for r in rows if r['dangling']}
rev={m:set() for m in mods}
for m,r in mods.items():
 for dep in r['imports']:rev[dep].add(m)
affected=set(stale);pending=list(stale)
while pending:
 for n in rev[pending.pop()]:
  if n not in affected:affected.add(n);pending.append(n)
order=[];done=set()
def visit(n):
 if n in done:return
 done.add(n)
 for dep in mods[n]['imports']:visit(dep)
 if n in affected:order.append(n)
for n in sorted(affected):visit(n)
scan=dict(status='incoherent',method='Lean serialized private-table existence preflight; final loaded-environment check still required',module_count=len(rows),declarations=sum(r['declarations'] for r in rows),edges=sum(r['edges'] for r in rows),imports_all_match=all(r['imports_match'] for r in rows),dangling_modules=[r for r in rows if r['dangling']],affected_count=len(affected),rebuild_order=order)
(B/'NER_SCAN.json').write_text(json.dumps(scan,indent=2)+'\n')
for name in ['NER_COHORT.jsonl','NER_MANIFEST.jsonl','NER_SCAN_ROWS.jsonl','NER_KNOWN.txt']:
 p=B/name;h=hashlib.sha256()
 with p.open('rb') as src,lzma.open(str(p)+'.xz','wb',preset=6) as dst:
  for data in iter(lambda:src.read(1048576),b''):h.update(data);dst.write(data)
 (B/(name+'.sha256')).write_text(h.hexdigest()+'\n')
print(json.dumps({k:scan[k] for k in ['module_count','declarations','edges','affected_count']}))
print('dangling modules',sorted(stale));print('order',order)
