"""All six add_preweighted instantiations and all eight actual literal-start
callers. Source RangeInclusive end is computed from the exact caller start/N.
"""
from pathlib import Path
import json,lzma,argparse,copy,hashlib
from scalar_constants592 import constants
from caller_observe592 import collect
from source_normalize583 import normalize
from initializer_source578 import compact,find
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(ll,g,t):
 fs={f['def_id']:f for f in ll['fun_decls']if f}
 for fid in[59,46,37,208]:assert compact(fs[fid]['body'])==t[str(fid)]
 vs,bs=constants(ll,fs);obs=[]
 for fid in[19,54,55,56,57]:
  b,changes=normalize(fs[fid]['body'],vs)
  for r in collect(b):
   if r['callee']!=59:continue
   arg=r['arguments'][1];assert arg and arg['expression']['op']=='literal';start=arg['expression']['value'];fun=r['source_call']['kind']['Call']['call']['func']['Regular'];n=literal(fun['generics']['const_generics'][0]);assert n is not None and n>0
   insts=[k for k,v in g['instances'].items()if v['id']==59 and literal(v['environment']['const_generics'][0])==n];assert len(insts)==1
   last=(start+n-1)//4;assert start+n<2**32 and last<24
   obs.append(dict(instance=insts[0],caller_id=fid,N=n,start=start,first=start//4,last=last,statement=r['statement'],source_call=r['source_call'],normalizations=changes))
 assert len(obs)==8
 assert sorted((e['caller'],e['callee'])for e in g['edges']if e['callee_id']==59)==sorted((next(k for k,v in g['instances'].items()if v['id']==r['caller_id']),r['instance'])for r in obs)
 # Exact first=start/4 and last=((start+N)-1)/4 source arithmetic.
 assert compact(find(fs[59]['body'],7074)['kind']['Assign'][1])['BinaryOp'][0]=={'Div':'Panic'}
 constructor=compact(find(fs[59]['body'],7107)['kind']['Call']['call']);assert constructor['func']['Regular']['kind']['Fun']=={'Regular':46}
 # End is private within the iterator: the full body template fixes constructor,
 # identity into_iter and sole next call, including all borrow/end/drop paths.
 return obs,bs

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'PREWEIGHTED-TEMPLATE-D592.json').read_text());obs,bs=certify(ll,g,t);controls={}
 for fid,sid,label in[(59,7107,'constructor_changed'),(59,7144,'next_changed'),(19,2629,'caller_start_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid);find(f['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_PreweightedIndices592227';s='import PV_B3P_InclusiveEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n';rows=[]
 for inst in sorted({r['instance']for r in obs}):
  for site in[29589,29594]:
   lemmas=[]
   for j,r in enumerate(q for q in obs if q['instance']==inst):
    label='certificate_'+inst.split(':')[1]+f'_{site}_{j}';lemmas.append(name+'.'+label);args=f'handler ⟨current,{r["last"]}#usize,exhausted⟩ {23-r["last"]} effects'
    s+=f'''/-- Actual {r['caller_id']}:{r['statement']}, start={r['start']}, N={r['N']}, last={r['last']}. -/
theorem {label} {{α : Type}} (handler : Str → Result Never) (current : Usize)
    (exhausted : Bool) (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_InclusiveEvents592227.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_InclusiveEvents592227.event_certificate {args} observed ran normal first second
#print axioms {label}
'''
   rows.append(dict(instance=inst,function_id=59,statement=site,lemma=lemmas[0],all_caller_lemmas=lemmas,actual_callers=[r for r in obs if r['instance']==inst]))
 x=dict(rows=rows,count=12,chunks=[name],constants=bs,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 all actual literal start/N callers and inclusive-next scalar frames plus named kernel guards',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in {D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'PREWEIGHTED-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=12,callers=8,check=a.check,controls=controls)))
if __name__=='__main__':main()
