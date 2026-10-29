"""Exhaustive statement-pattern check, plus exact named source-model chain.
No whole-callback native closure is inferred from these local associations.
"""
from pathlib import Path
import json,hashlib,re
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';I=json.loads((D/'resume9/body-inventory.json').read_text());F=next(f for f in I['files']if f['family']=='terminal');sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(Path(F['source']).read_bytes())==F['source_sha256']
expected={
'reconstruct_10':'''{let mut acc=view[9];let mut index=9usize;while index>0{index-=1;acc=acc.add(acc).add(view[index]);}acc}''',
'equality_value':'''{let mut product=equality_factor(left[0],right[0]);let mut index=1usize;while index<left.len(){product=product.mul(equality_factor(left[index],right[index]));index+=1;}product}'''}
models={
'reconstruct_10':['PV_B3P_ReconstructNative14227','PV_B3P_ReconstructBinding9227','PV_B3P_ReverseLoop9227','PV_B3P_SelectIndex227','PV_B3P_ArrayWrite227'],
'equality_value':['PV_B3P_EqualityNative14227','PV_B3P_EqualityBinding9227','PV_B3P_UsizeLoop9227','PV_B3P_SelectIndex227']}
rows=json.loads((O/'immutable-native-associations.json').read_text())
for name,s in expected.items():
 r=next(r for r in I['bodies']if r['family']=='terminal'and r['key']==name+'#0');tokens=r['source']['tokens'];body=tokens[tokens.index('{'):];want=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+[A-Za-z_0-9]*|[^\s]',s)
 assert body==want,(name,body,want)
 negative=want.copy();negative[negative.index('9' if name=='reconstruct_10' else '1usize')]='8'if name=='reconstruct_10'else'2usize';assert negative!=body
 record=next(r for r in rows if r['function']==name);record.update(statement_pattern_complete=True,matched_negative_control='changed initial read/index rejected by exact grammar',models=[dict(module=m,sha256=sha((D/'lean'/(m+'.lean')).read_bytes()))for m in models[name]],native_status='Exact source-to-interpreter statement map and complete-Result local law; full source-index/primitive/dependency association remains OPEN. Do not count as fully composed own-1 BOUND.')
(O/'immutable-native-associations.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(local_statement_associations=len(rows),new_fully_composed_bound=0)))
