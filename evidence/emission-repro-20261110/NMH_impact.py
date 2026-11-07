#!/usr/bin/env python3
"""Read-only ledger24 root intersection with NKT's conservative name mapping."""
from pathlib import Path
import json,lzma,hashlib,collections
E=Path(__file__).resolve().parent;A=E.parent/'emission-audit-20261109';L=E.parent/'ledger24-20261110'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 inv=json.loads((E/'NMH_INVENTORY.json').read_text());blobs={b['blob']:b for b in inv['blobs']}
 aud=json.loads(lzma.decompress((A/'NKT_AUDIT.json.xz').read_bytes()));sup=json.loads(lzma.decompress((A/'NKT_SUPERSET.json.xz').read_bytes()))
 names=collections.defaultdict(set);defs=collections.defaultdict(list)
 for f in aud['functions']+sup['functions']:
  h=f['emission_sha256']
  if h not in blobs:continue
  for n in f.get('root_reachability_name_matches',[]):names[n].add(h)
  defs[h].append(dict(definition=f['definition'],line=f['emission_line'],sha256=f['emitted_definition_sha256'],rust_symbol=f['rust_symbol']))
 # Exact names from namespace declarations supplement the NKT conservative mapping.
 for h,b in blobs.items():
  for ns in b['namespace']:
   for d in b['definitions']:names[ns+'.'+d].add(h)
 ledger=json.loads(lzma.decompress((L/'NLX_LEDGER.json.xz').read_bytes()));rows=collections.defaultdict(set)
 for r in ledger['rows']:
  if r['status']=='CLOSED':
   for root in r.get('root_owners',[]):rows[root['root']].add(r['row'])
 # Reuse NKT indexed receipts where NLX does not have a matching root filename.
 nkt={r['root']:r for r in json.loads((A/'NKT_ROOT_REACHABILITY.json').read_text())}
 hits=collections.defaultdict(lambda:collections.defaultdict(set));receipts=[];missing=[]
 for root,rr in sorted(rows.items()):
  found=list(L.glob('*_'+root+'_REACHABLE.txt.xz'))
  p=found[0] if len(found)==1 else None
  if p is None and root in nkt:
   for r in nkt[root]['reachable_receipts']:
    q=Path(r['path'])
    if q.exists():p=q;break
  if p is None:missing.append(dict(root=root,rows=sorted(rr),reason='No local archived root list; not treated as absence'));continue
  raw=lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes();side=p.with_suffix('.sha256')
  if side.exists():assert side.read_text().strip().split()[0]==sha(raw),(p,'sidecar')
  reach=set(raw.decode().splitlines());used=reach.intersection(names)
  for n in used:
   for h in names[n]:hits[h][root].add(n)
  receipts.append(dict(root=root,path=str(p),sha256=sha(raw),rows=sorted(rr),matching_names=len(used)))
 out=[]
 for h,b in blobs.items():
  roots=[dict(root=r,names=sorted(ns),rows=sorted(rows[r])) for r,ns in sorted(hits[h].items())]
  out.append(dict(blob=h,affected_CLOSED_rows=sorted({rr for r in roots for rr in r['rows']}),reaching_roots=roots,mapping='Conservative NKT name matches and exact namespace/definition candidates; selected source-to-object alias ambiguity retained.',unresolved_root_lists=len(missing)))
 raw=json.dumps(dict(ledger_sha256=sha((L/'NLX_LEDGER.json.xz').read_bytes()),closed_rows=sum(r['status']=='CLOSED' for r in ledger['rows']),roots=len(rows),missing_root_lists=missing,receipts=receipts,blobs=out),indent=2).encode();(E/'NMH_ROW_IMPACT.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NMH_ROW_IMPACT.json.sha256').write_text(sha(raw)+'\n')
 print(json.dumps(dict(blobs=len(out),roots=len(rows),checked=len(receipts),missing=len(missing),affected_blobs=sum(bool(x['affected_CLOSED_rows']) for x in out))))
if __name__=='__main__':main()
