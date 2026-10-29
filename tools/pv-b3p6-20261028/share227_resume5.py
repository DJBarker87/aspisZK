"""Share repeated pure right-component arrays in the prepared helper.
A token roundtrip expands every shared use and removes the introduced let. The
initializer appears before its first use, after all its input bindings.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-arraytypes-resume5.lean.txt';s=p.read_text();a=s.index('/-- [pv_b3p6_reference227::reference_field::qm31_sum_products3_prepared]');b=s.index('\n/-- [',a+1);old=s[a:b];groups={};edits=[]
for m in re.finditer(r'\(Array\.make 3#usize \[',old):
 depth=1;i=m.start()+1
 while depth:depth+=(old[i]=='(')-(old[i]==')');i+=1
 expr=old[m.start():i]
 if 'right_sum'not in expr or expr.count('Array.make')!=4:continue
 key=re.sub(r'\s+',' ',expr)
 groups.setdefault(key,[]).append((m.start(),i,expr))
assert len(groups)==3 and all(len(v)==3 for v in groups.values()),[(k[:60],len(v))for k,v in groups.items()]
for j,occ in enumerate(groups.values()):
 name=f'right_components227_{j}'
 first=occ[0];line=old.rfind('\n  let ',0,first[0])+1
 init='  let '+name+' : Array (Array aspis_core.field.M31 3#usize) 3#usize := '+first[2]+'\n'
 edits.append((line,line,init))
 for start,end,expr in occ:edits.append((start,end,name))
new=old
for start,end,value in sorted(edits,reverse=True):new=new[:start]+value+new[end:]
restored=new
for j,occ in enumerate(groups.values()):
 name=f'right_components227_{j}';decl='  let '+name+' : Array (Array aspis_core.field.M31 3#usize) 3#usize := '+occ[0][2]+'\n';assert restored.count(decl)==1
 restored=restored.replace(decl,'');restored=re.sub(r'\b'+name+r'\b',lambda m:occ[0][2],restored)
token=lambda x:re.findall(r'\w+|[^\s]',x)
assert token(restored)==token(old)
q=D/'ported227-shared-resume5.lean.txt';q.write_text(s[:a]+new+s[b:]);(D/'share227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),shared_pure_arrays=3,uses_each=3,expansion_token_roundtrip=True,effectful_call_order_unchanged=True),indent=2)+'\n');print('shared',len(groups))
