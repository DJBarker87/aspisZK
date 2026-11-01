"""Check the new sum interval's complete std code-item set against D540.
New ordinary items fail closed. No solver, compilation, or source mutation.
"""
from pathlib import Path
import json,lzma,hashlib
D=Path('evidence/pv-b3p6-20261028/resume17');sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((D/'K3-STD-PARITY-D540.json').read_text())
known={(r['name'],r['source'],str(r['location'].get('line'))):r for r in old['rows']}
rows=[];excluded=[]
for run in ['K73949','K73950']:
 p=D/(run+'-symbols/index.json');x=json.loads(p.read_text());selected=0
 for a in x['records']:
  if not a['harness']['original_file'].endswith('equivalence_k3_17.rs'):
   excluded.append(dict(run=run,metadata=a['metadata'],reason='different historical proof crate'));continue
  selected+=1;f=p.parent/Path(a['symbol_dump']).name;b=f.read_bytes();assert sha(b)==a['symbol_dump_sha256']
  table=next(v['symbolTable']for v in json.loads(lzma.decompress(b))if 'symbolTable'in v)
  assert not any('shared_callee16' in name for name in table)
  for symbol,v in table.items():
   if v.get('type',{}).get('id')!='code':continue
   loc=v.get('location',{});path=loc.get('file','')
   if '/library/'not in path:continue
   rel=path.split('/library/',1)[1]
   if not rel.startswith(('core/','alloc/','std/')):continue
   name=v.get('prettyName',symbol);key=(name,rel,str(loc.get('line')))
   r=known.get(key);assert r is not None,('new item requires source argument',key)
   assert r['status']=='IDENTICAL' or r['classification'].startswith('V370') or r['name']=='core::ub_checks::check_language_ub',r
   rows.append(dict(run=run,name=name,source=rel,line=loc.get('line'),prior_status=r['status'],transfer='token identity'if r['status']=='IDENTICAL'else 'retained V370'if r['classification'].startswith('V370')else "STD-STRUCTURAL-D542 argument ub (k''')"))
 assert selected,run
out=dict(complete_std_item_mapping=True,rows=rows,excluded_records=excluded,new_unargued_items=[],K3='no shared static oracle in selected dedicated proof crate; wrapper static-free source check retained; controls matched',label="Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''')",V370='retained, owner D381/D386; no intrinsic semantics credit',status='Transfer eligible only if K73950 verdict PASS and K73949 has intended failed assertion',endpoint_premise_changes=dict(removed=[],added=[],weakened=[]))
(D/'STD-K50-D542.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(items=len(rows),new_unargued=[])))
