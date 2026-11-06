#!/usr/bin/env python3
"""Reuse existing checked raw-walker reachability lists; no Lean run."""
import json,lzma,pathlib,hashlib,collections,base64
from NKT_checker import Git,sha
P=pathlib.Path(__file__).parent

def main():
 a=json.load(open(P/'NKT_AUDIT.json'));g=Git(a['audit_revision']);ledger=json.loads(lzma.decompress(g.read('evidence/ledger19-20261108/NKN_LEDGER.json.xz')))
 index=collections.defaultdict(list)
 dirs=['evidence/ledger19-20261108/','evidence/circle-points-20261108/','evidence/terminal4-20261108/','evidence/batch-merkle3-20261108/']
 for p in g.entries:
  if not any(p.startswith(d) for d in dirs):continue
  if p.endswith(('_REACHABLE.txt.xz','_REACHABLE.txt.xz.b64.txt')):
   # Root names can contain underscores; search by exact suffix later.
   index[p.split('/')[-1]].append(p)
 paths=[p for ps in index.values() for p in ps]
 roots=collections.defaultdict(set)
 for r in ledger['rows']:
  if r['status']=='CLOSED':
   for rt in r.get('root_owners',[]):roots[rt['root']].add(r['row'])
 for inp in a['pending_inputs']:
  for r in inp['data'].get('functions',[]):
   for rt in r.get('roots',r.get('lean_roots',[])):
    roots[rt].update('PENDING:'+str(x) for x in r.get('rows',[r.get('row')]))
 records=[];unique=set();allnames=set()
 for root,rs in sorted(roots.items()):
  matches=[p for p in paths if p.endswith(('_'+root+'_REACHABLE.txt.xz','_'+root+'_REACHABLE.txt.xz.b64.txt'))]
  preferred=[p for p in matches if p.startswith('evidence/ledger19-20261108/')]
  if preferred:matches=preferred
  counts=[];references=set()
  for p in matches:
   raw=base64.b64decode(g.read(p)) if p.endswith('.b64.txt') else g.read(p);b=lzma.decompress(raw);side=p.removesuffix('.b64.txt')[:-3]+'.sha256';expected=g.text(side).strip().split()[0] if side in g.entries else None
   if expected and expected!=sha(b):raise RuntimeError('Reachability hash mismatch '+p)
   names=set(b.decode().splitlines());allnames.update(names);references.update(n for n in names if '.batch_tree' in n)
   counts.append({'path':p,'uncompressed_sha256':sha(b),'hash_sidecar_matches':expected==sha(b) if expected else None,'names':len(names)})
  if not counts and P.joinpath('NKT_PENDING_REACHABILITY.json.xz').exists():
   recovered=json.loads(lzma.open(P/'NKT_PENDING_REACHABILITY.json.xz').read())
   for item in recovered:
    if item['root']==root:
     names=set(item['text'].splitlines());allnames.update(names);references.update(n for n in names if '.batch_tree' in n)
     assert sha(item['text'].encode())==item['sha256']
     counts.append({'path':'NKT_PENDING_REACHABILITY.json.xz#'+root,'host_path':item['path'],'uncompressed_sha256':item['sha256'],'names':len(names),'recovered_read_only':True})
  records.append({'root':root,'rows':sorted(rs),'reachable_receipts':counts,'batch_tree_dependencies':sorted(references),'verdict':'MISSING_REACHABILITY_RECEIPT' if not counts else ('REQUIRES_STATEMENT_REVIEW' if references else 'INSENSITIVE_NO_BATCH_TREE_IN_CHECKED_CLOSURE')})
 # Inventory which emitted names are actually present in the union of checked roots.
 bylast=collections.defaultdict(set)
 for n in allnames:bylast[n.split('.')[-1]].add(n)
 for f in a['functions']:
  n=f['definition'];f['root_reachability_name_matches']=sorted(x for x in bylast[n.split('.')[-1]] if x==n or x.endswith('.'+n))
 a['reachability_summary']={'root_count':len(records),'roots_with_receipt':sum(bool(r['reachable_receipts']) for r in records),'roots_referencing_batch_tree':sum(bool(r['batch_tree_dependencies']) for r in records),'missing_roots':[r['root'] for r in records if not r['reachable_receipts']]}
 P.joinpath('NKT_ROOT_REACHABILITY.json').write_text(json.dumps(records,indent=1)+'\n')
 P.joinpath('NKT_AUDIT.json').write_text(json.dumps(a,separators=(',',':'))+'\n')
 print(json.dumps(a['reachability_summary']))
if __name__=='__main__':main()
