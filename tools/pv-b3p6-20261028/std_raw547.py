"""Fail-closed mapping of every reached std code item in the repaired raw pair."""
from pathlib import Path
import json,lzma,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';P=D/'resume17'
sha=lambda b:hashlib.sha256(b).hexdigest()
known={}
for n in ['STD-PARITY-D540.json','K3-STD-PARITY-D540.json']:
 for r in json.loads((P/n).read_text())['rows']:
  known[(r['name'],r['source'],str(r['location'].get('line')))]=r
args=json.loads((P/'STD-STRUCTURAL-D542.json').read_text());assert not args['unargued_ordinary_items']
structural={(r['name'],r['source'],str(r['kani_line'])):r for r in args['items']}
rows=[];unargued=[];excluded=[]
for run in ['K79106','K79107']:
 p=R/(run+'-symbols/index.json');idx=json.loads(p.read_text());assert idx['records'],run
 selected=0
 for a in idx['records']:
  if not a['harness']['original_file'].endswith('equivalence18.rs'):
   excluded.append(dict(run=run,metadata=a['metadata']));continue
  selected+=1;f=p.parent/Path(a['symbol_dump']).name;b=f.read_bytes();assert sha(b)==a['symbol_dump_sha256']
  table=next(v['symbolTable']for v in json.loads(lzma.decompress(b))if 'symbolTable'in v)
  assert not any('shared_callee16' in n for n in table)
  for symbol,v in table.items():
   if v.get('type',{}).get('id')!='code':continue
   loc=v.get('location',{});path=loc.get('file','')
   if '/library/'not in path:continue
   rel=path.split('/library/',1)[1]
   if not rel.startswith(('core/','alloc/','std/')):continue
   name=v.get('prettyName',symbol);key=(name,rel,str(loc.get('line')));r=known.get(key)
   if r is None:unargued.append(dict(run=run,key=key,reason='not in pinned D540 inventory'));continue
   if r['status']=='IDENTICAL':route='source token identity'
   elif r['classification'].startswith('V370'):route='retained V370 compiler-cohort item'
   elif key in structural:
    x=structural[key];assert x['verdict']=='ARGUED under k-triple-prime',x['verdict'];route='D542 exact per-item structural argument: '+x['argument_key']
   else:unargued.append(dict(run=run,key=key,reason='ordinary differing item lacks structural argument'));continue
   rows.append(dict(run=run,name=name,source=rel,line=loc.get('line'),prior_status=r['status'],transfer=route,symbol=symbol))
 assert selected==1,(run,selected)
out=dict(items=rows,excluded=excluded,new_unargued_items=unargued,complete_std_item_mapping=not unargued,label="Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''')",V370='retained D381/D386, includes generated closures, intrinsics, derived copy/drop and runtime lowering',K3='same original raw harness names, no writable static; matched XOR control required',status='transfer requires raw positive PASS and exact intended failed control; this script alone supplies neither')
(R/'STD-RAW-D547.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(items=len(rows),unargued=unargued)));assert not unargued
