"""Actual array VALUES and inclusive-range VALUES at fold callbacks;
immutable literal range arrays supplied to sum_high. Cursor bounds are never
substituted for callback value bounds.
"""
from pathlib import Path
import json,lzma,hashlib,copy,argparse
from initializer_source578 import compact,find,nodes
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
FIDS=[17,18,43,44,45,47,55,191,195,197,207,217,231,325,329]
def ranges(f):
 env={};out=[]
 def operand(o):
  if'Const'in o:return literal(o['Const'])
  tag,p=next(iter(o.items()));k=p['kind']
  if 'Local'in k:return env.get(k['Local'])
  if 'Projection'in k and k['Projection'][1]=='Deref':return env.get(k['Projection'][0]['kind'].get('Local'))
  return None
 for st in f['body']['Structured']['body']['statements']:
  k=st['kind'];v=None
  if not isinstance(k,dict):continue
  if'Assign'in k:
   dest,rhs=k['Assign']
   if'Use'in rhs:v=operand(rhs['Use'][0])
   elif'Ref'in rhs:
    p=rhs['Ref']['place']['kind'];v=operand({'Copy':{'kind':p}})
   elif'Aggregate'in rhs:
    tag,args=rhs['Aggregate'];marks=[operand(o)for o in args]
    if tag.get('Adt',[{}])[0].get('id')=={'Adt':25}and all(isinstance(v,int)for v in marks):v=('range',*marks)
    elif'Array'in tag and all(v is not None for v in marks):v=('array',marks)
   if'Local'in dest['kind']:env[dest['kind']['Local']]=v
  elif'Call'in k:
   c=k['Call']['call'];fun=c['func'].get('Regular',{}).get('kind',{}).get('Fun',{})
   if fun=={'Builtin':'ArrayToSliceShared'}:v=operand(c['args'][0])
   if fun=={'Regular':43}:
    r=operand(c['args'][1]);assert r and r[0]=='array'and all(q[0]=='range'and len(q)==3 for q in r[1]);out.append(dict(statement=st['id'],ranges=r[1]))
   env[c['dest']['kind'].get('Local')]=v
 return out

def certify(ll,g,t):
 fs={f['def_id']:f for f in ll['fun_decls']if f}
 for fid in FIDS:assert compact(fs[fid]['body'])==t[str(fid)]
 rs=[]
 for fid in[17,55,231]:
  rr=ranges(fs[fid]);assert len(rr)==1
  for row in rr:
   assert all(0<=a<=b<=64 for _,a,b in row['ranges']);rs.append(dict(caller_id=fid,**row))
 assert len([e for e in g['edges']if e['callee_id']==43])==3
 agg=find(fs[18]['body'],2360)['kind']['Assign'][1]['Aggregate'];values=[literal(o['Const'])for o in agg[1]];assert values==[1,9,10]and all(v<16 for v in values)
 c=compact(find(fs[18]['body'],2385)['kind']['Call']['call']);assert c['func']['Regular']['kind']['Fun']=={'Regular':46}and[literal(o['Const'])for o in c['args']]==[2,8]
 # Each callback receives tuple field1, the VALUE supplied by its wrapper.
 for fid,extract in[(195,9462),(197,9518)]:
  assert compact(find(fs[fid]['body'],extract)['kind']['Assign'][1]['Use'][0])=={'Move':{'kind':{'Projection':[{'kind':{'Local':2}},{'Field':[{'Tuple':2},1]}]}}}
 paths={195:[325,329,207,45,18],197:[325,217,47,18]};chains={}
 for fid,path in paths.items():
  cur=next(k for k,v in g['instances'].items()if v['id']==fid);chain=[]
  for parent in path:
   es=[e for e in g['edges']if e['callee']==cur];assert es and {g['instances'][e['caller']]['id']for e in es}=={parent};assert len({e['caller']for e in es})==1
   chain.extend(es);cur=es[0]['caller']
  chains[str(fid)]=chain
 return values,rs,chains

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'FOLD-TEMPLATE-D592.json').read_text());values,rs,chains=certify(ll,g,t);controls={}
 for fid,sid,label in[(18,2360,'array_value_changed'),(18,2385,'inclusive_value_domain_changed'),(195,9462,'callback_tuple_value_changed'),(43,3974,'range_value_forward_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid);find(f['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_FoldIndices592227';s='import PV_B3P_TableEvents592227\nimport PV_B3P_InclusiveEvents592227\nimport PV_B3P_RangeEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n';rows=[]
 for v in values:s+=f'def value{v} : Fin 16 := ⟨{v},by decide⟩\n'
 s+='def sourceValues : List (List (Fin 16)) := [[value1,value9,value10]]\n'
 cases=[(195,29757,'array_value','PV_B3P_TableEvents592227','16 sourceValues 0 cursor effects','(cursor : Nat)'),(197,29762,'inclusive_value','PV_B3P_InclusiveEvents592227','handler ⟨current,8#usize,exhausted⟩ 7 effects','(handler : Str → Result Never) (current : Usize) (exhausted : Bool)')]
 ranges_lemmas=[]
 for j,r in enumerate(rs):
  for k,(_,start,end)in enumerate(r['ranges']):
   label=f'range_{j}_{k}';ranges_lemmas.append(name+'.'+label);cases.append((43,29350,label,'PV_B3P_RangeEvents578227',f'handler ⟨current,{end}#usize⟩ {64-end} effects','(handler : Str → Result Never) (current : Usize)'))
 for fid,site,label,ns,args,params in cases:
  s+=f'''/-- Actual VALUE-domain source event at {fid}:{site}. -/
theorem {label} {{α : Type}} {params} (effects : List (Result Unit)) (observed : IndexState)
    (ran : {ns}.sourceEvent {args} = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
#print axioms {label}
'''
 for fid,site,label in[(195,29757,'array_value'),(197,29762,'inclusive_value'),(43,29350,'range_0_0')]:rows.append(dict(instance=next(k for k,v in g['instances'].items()if v['id']==fid),function_id=fid,statement=site,lemma=name+'.'+label,all_caller_lemmas=ranges_lemmas if fid==43 else[name+'.'+label]))
 x=dict(rows=rows,count=3,chunks=[name],array_values=values,literal_ranges=rs,source_chains=chains,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 actual array/range VALUES and callback tuple forwarding plus named kernel guards',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',native_borrow_restoration=False,whole_caller_association=False,premises_removed=[])
 for p,t in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'FOLD-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=3,check=a.check,controls=controls)))
if __name__=='__main__':main()
