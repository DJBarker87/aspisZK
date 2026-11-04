"""Bind both actual expand callers to symbolic outer-depth/width and private
countdown invariants. Never normalize the generated field recurrence.
"""
from pathlib import Path
import json,lzma,hashlib,copy,argparse
from initializer_source578 import compact,find,nodes
from fixed_indices572 import literal
from frame_indices578 import root,dicts
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(ll,g,t):
 fs={f['def_id']:f for f in ll['fun_decls']if f}
 for fid in[42,189]:assert compact(fs[fid]['body'])==t[str(fid)]
 callers=[]
 for sid in[3859,3866]:
  c=find(fs[42]['body'],sid)['kind']['Call']['call'];f=c['func']['Regular'];assert f['kind']['Fun']=={'Regular':189};n=literal(f['generics']['const_generics'][0]);start,count=[literal(o['Const'])for o in c['args'][1:]];assert start+count<=10 and 2**count==n
  inst=next(k for k,v in g['instances'].items()if v['id']==189 and literal(v['environment']['const_generics'][0])==n);callers.append(dict(instance=inst,source_call=sid,N=n,start=start,count=count))
 assert len([e for e in g['edges']if e['callee_id']==189])==2
 # Bind the exact private scalar stores and forbid address escape.
 writes={slot:[]for slot in[6,7,16]}
 for st in nodes(fs[189]['body']):
  k=st['kind']
  if not isinstance(k,dict):continue
  if'Assign'in k:
   dest,rhs=k['Assign'];slot=root(dest)
   if slot in writes:writes[slot].append(st['id'])
   for tag in['Ref','RawPtr']:
    if tag in rhs:assert root(rhs[tag]['place'])not in writes
 assert writes=={6:[9111,9240],7:[9113,9241],16:[9150,9157]}
 assert compact(find(fs[189]['body'],9157)['kind']['Assign'][1])['BinaryOp'][0]=={'Sub':'Wrap'}
 assert compact(find(fs[189]['body'],9240)['kind']['Assign'][1])['BinaryOp'][0]=={'Mul':'Wrap'}
 assert compact(find(fs[189]['body'],9241)['kind']['Assign'][1])['BinaryOp'][0]=={'Add':'Wrap'}
 return callers,writes

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'EXPAND-TEMPLATE-D592.json').read_text());callers,writes=certify(ll,g,t);controls={}
 for fid,sid,label in[(42,3859,'caller_domain_changed'),(189,9157,'inner_decrement_changed'),(189,9240,'width_update_changed'),(189,9241,'coordinate_update_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid);find(f['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_ExpandIndices592227';s='import PV_B3P_ExpandFrame592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n';rows=[]
 for r in callers:
  for site,kind in[(29747,'point'),(29732,'parent'),(29737,'left'),(29742,'right')]:
   label=f'certificate_{r["N"]}_{site}';args=f'.{kind} {r["start"]} {r["count"]} {r["N"]} outer inner effects';rows.append(dict(instance=r['instance'],function_id=189,statement=site,lemma=name+'.'+label,caller=r))
   s+=f'''/-- Actual expand caller42:{r['source_call']}, scalar source189:{site}. -/
theorem {label} {{α : Type}} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate {args} observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=rows,count=8,chunks=[name],actual_callers=callers,private_scalar_writes=writes,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 exact caller/loop scalar closed-form projections plus kernel depth/width/countdown laws and guards',validation_status='PREPARATION; focused compiles and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'EXPAND-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=8,check=a.check,controls=controls)))
if __name__=='__main__':main()
