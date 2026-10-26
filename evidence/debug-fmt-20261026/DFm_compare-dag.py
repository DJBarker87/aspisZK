"""Compare shared Expr graphs; binder names omitted by the serializer.
Every child fingerprint is SHA-256 of its full canonical node and child
fingerprints. No 64-bit Expr hash is used as comparison evidence.
"""
from pathlib import Path
import json,hashlib,sys
B=Path(sys.argv[1]);rows=json.loads(Path(sys.argv[2]).read_text());results=[]
rename={}
for ns in ['AspisR1RecordParser','AspisR1PrefixAggregateParser']:
 p=ns+'.r1_wire.'
 rename[p+'Error.Insts.CoreFmtDebug.fmt.match_1']=p+'Error.Insts.CoreCmpPartialEqError.eq.match_1'
 for s in ['parse_record','validate_record_fields_loop.body']+(['Prefix.parse'] if 'PrefixAggregate' in ns else []):rename[p+s+'.match_3']=p+s+'.match_2'
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(p):
 data=json.loads(p.read_text());hs=[]
 for i,node in enumerate(data['nodes']):
  n=dict(node)
  if 'children' in n:
   assert all(j<i for j in n['children']),(i,n)
   n['children']=[hs[j] for j in n['children']]
  if 'name' in n:n['name']=rename.get(n['name'],n['name'])
  hs.append(sha(n))
 decls={}
 for r in data['rows']:
  r=dict(r);r['type']=hs[r['type']];r['value']=None if r['value'] is None else hs[r['value']];decls[r['name']]=r
 return decls,data
for j,row in enumerate(rows):
 before=B/f'DFm_split-{j:02d}-before.json';after=B/f'DFm_split-{j:02d}-after.json'
 a,ar=load(before);z,zr=load(after);changed=[];same=[]
 for n in sorted(a.keys()&z.keys()):
  fields=[k for k in a[n] if a[n][k]!=z[n][k]]
  if fields:changed.append(dict(name=n,fields=fields))
  same.append(dict(name=n,before_sha256=sha(a[n]),after_sha256=sha(z[n]),equal=not fields))
 refs=sorted({n['name'] for n in zr['nodes'] if n.get('kind') in ['const','proj'] and '.CoreFmtDebug' in n['name']})
 result=dict(module=row['module'],before_declarations=len(a),after_declarations=len(z),before_nodes=len(ar['nodes']),after_nodes=len(zr['nodes']),added=sorted(z.keys()-a.keys()),removed=sorted(a.keys()-z.keys()),changed=changed,all_retained_equal=a.keys()==z.keys() and not changed,retained=same,nonstandard_after=[dict(name=r['name'],axioms=r['axioms']) for r in z.values() if set(r['axioms'])-{'propext','Classical.choice','Quot.sound'}],formatter_references_after=refs,before_snapshot_sha256=hashlib.sha256(before.read_bytes()).hexdigest(),after_snapshot_sha256=hashlib.sha256(after.read_bytes()).hexdigest(),snapshot_sizes=[before.stat().st_size,after.stat().st_size])
 results.append(result);print(row['module'],'equal',result['all_retained_equal'],'declarations',len(z),'changes',changed[:4])
x=dict(method='Shared-expression DAG serialized by Lean; compare SHA-256 of full recursively canonicalized nodes; binder names omitted, seven explicitly listed matcher names renamed; all other node fields including metadata and reduction hints retained',renaming=rename,all_retained_equal=all(r['all_retained_equal'] for r in results),modules=results)
(B/'DFm_importers-semantic-comparison.json').write_text(json.dumps(x,indent=2)+'\n')
