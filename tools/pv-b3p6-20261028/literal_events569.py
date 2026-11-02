"""Emit named small-numeral bounds for exact literal index events only."""
from pathlib import Path
import json,lzma,hashlib
R=Path('evidence/pv-b3p6-20261028/resume18');I=R/'imports-b3q/pv-b3q2-20261031'
x=json.loads(lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes()))['translated']
g=json.loads((I/'direct3-instantiated-callcone.json').read_text());funs={f['def_id']:f for f in x['fun_decls']if f};rows=[]
def visit(v,caller):
 if isinstance(v,list):
  for y in v:visit(y,caller)
 elif isinstance(v,dict):
  if 'kind'in v and isinstance(v['kind'],dict)and 'Call'in v['kind']:
   c=v['kind']['Call']['call'];f=c['func'].get('Regular',{});b=f.get('kind',{}).get('Fun',{}).get('Builtin',{})
   if isinstance(b,dict)and 'Index'in b and b['Index']['is_array'] and not b['Index']['is_range'] and 'Const'in c['args'][1]:
    i=c['args'][1]['Const']['kind']['Literal']['Scalar']['Unsigned'];n=f['generics']['const_generics'][0]['kind']['Literal']['Scalar']['Unsigned']
    assert i[0]==n[0]=='Usize';index,length=int(i[1]),int(n[1]);assert 0<=index<length<=1024
    rows.append(dict(instance=caller,statement=v['id'],span=v['span'],index=index,length=length,local_theorem='PV_B3P_LiteralEvents569227.site_'+str(v['id']),scope='exact source operand and const-generic bound; numeric failure/formatting branch excluded; pointer realization separate'))
  for y in v.values():visit(y,caller)
for caller,i in g['instances'].items():
 if funs[i['id']].get('body'):visit(funs[i['id']]['body'],caller)
unique={r['statement']:r for r in rows}
s='import PV_B3P_PreconditionFormatting569227\nnamespace PV_B3P_LiteralEvents569227\nopen Aeneas Aeneas.Std PV_B3P_PreconditionFormatting569227\nset_option autoImplicit false\n'
for sid,r in unique.items():
 s+=f"theorem bound_{sid} : ({r['index']} : Nat) < {r['length']} := by decide\n"
 s+=f"theorem site_{sid} (panic : Result Unit) :\n    check panic (({r['index']} : Nat) < {r['length']}) = .ok () :=\n  check_safe _ _ bound_{sid}\n#print axioms bound_{sid}\n#print axioms site_{sid}\n"
s+='end PV_B3P_LiteralEvents569227\n';p=Path('evidence/pv-b3p6-20261028/lean/PV_B3P_LiteralEvents569227.lean');p.write_text(s)
(R/'LITERAL-EVENTS-D569.json').write_text(json.dumps(dict(events=rows,unique_statements=len(unique),source_sha256=hashlib.sha256(s.encode()).hexdigest(),not_a_whole_cone_certificate=True),indent=2)+'\n');print('literal source events',len(rows),'unique statements',len(unique))
