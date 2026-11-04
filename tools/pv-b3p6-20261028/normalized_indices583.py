"""Generate named guards after checked scalar constant/metadata normalization."""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from source_normalize583 import constants,normalize
from specialized_indices578 import instantiate
from range_indices578 import seeds
from dominated_indices578 import collect
from frame_indices578 import collect as frames
from initializer_source578 import compact
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D580.json').read_text());remaining={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['remaining']}
 # Complete source len primitive already used by metadata_source580, checked again.
 assert compact(fs[23]['body']['Structured']['body']['statements'])==[{'id':3195,'kind':{'StorageLive':0}},{'id':3196,'kind':{'Assign':[{'kind':{'Local':0}},{'Use':[{'Copy':{'kind':{'Projection':[{'kind':{'Local':1}},'PtrMetadata']}}},'No']}]}},{'id':3197,'kind':{'StorageDead':1}},{'id':3198,'kind':'Return'}]
 vs,bindings=constants(ll,fs);rows=[];sources=[]
 for inst,v in g['instances'].items():
  original=fs[v['id']].get('body')
  if not isinstance(original,dict):continue
  subst=[];body=instantiate(original,v['environment']['const_generics'],subst)if v['environment']['const_generics']else original
  body,changes=normalize(body,vs);sd,ff=seeds(body);new=[]
  for route,rs in [('dominated',collect(body)),('range',collect(body,sd)),('fixed',frames(body)[0])]:
   for r in rs:
    if(inst,r['statement'])in remaining:
     remaining.remove((inst,r['statement']));row=dict(instance=inst,function_id=v['id'],route=route,**r);rows.append(row);new.append(r['statement'])
  if new:sources.append(dict(instance=inst,original_sha256=sha(json.dumps(original,sort_keys=True).encode()),normalized_sha256=sha(json.dumps(body,sort_keys=True).encode()),normalizations=changes,const_substitutions=subst,range_frames=ff,statements=new))
 # New normalization controls; old frame/range/dominance controls remain applicable.
 controls={}
 changed=copy.deepcopy(ll)
 for glob in changed['global_decls']:
  if glob and glob['def_id']in vs:glob['global_kind']='Static'
 assert not constants(changed,fs)[0];controls['mutable_static_is_not_named_const']='rejected'
 changed=copy.deepcopy(fs)
 for glob in bindings:
  changed[glob['initializer']]['body']['Structured']['body']['statements'].insert(1,dict(id=-1,kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':0}}}}}))
 assert not constants(ll,changed)[0];controls['initializer_effect_or_extra_store']='rejected'
 # Minimal actual syntax from one captured metadata origin, including generics.
 orig=fs[9]['body'];_,normalization_controls=normalize(orig,{})
 from initializer_source578 import find
 obs=next(n for n in normalization_controls if n['kind']=='slice_metadata');co=copy.deepcopy(find(orig,obs['coercion']));lc=copy.deepcopy(obs['source']);arg=lc['kind']['Call']['call']['args'][0];slot=next(iter(arg.values()))['kind']['Local'];dest=co['kind']['Call']['call']['dest']['kind']['Local'];assert slot==dest
 def fixture(middle):return {'Structured':{'body':{'statements':[co,*middle,lc]}}}
 assert any(n['kind']=='slice_metadata'for n in normalize(fixture([]),{})[1])
 invalid={
  'coercion_destination_clobbered':{'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':slot}}}}},
  'coercion_result_moved':{'Call':{'call':{'func':{},'args':[{'Move':{'kind':{'Local':slot}}}],'dest':{'kind':{'Local':999}}}}},
  'metadata_scope_ended':{'StorageDead':slot},
  'metadata_loop_boundary':{'Loop':{'statements':[]}},
 }
 for label,k in invalid.items():
  assert not any(n['kind']=='slice_metadata'for n in normalize(fixture([dict(id=-1,kind=k)]),{})[1]);controls[label]='no scalar rewrite emitted'
 chunks=[];outputs={}
 for offset in range(0,len(rows),24):
  name=f'PV_B3P_NormalizedIndices583227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_RangeEvents578227\nimport PV_B3P_DominatedEvents578227\nimport PV_B3P_FixedIndex572227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
  for j,r in enumerate(rows[offset:offset+24],offset):
   r['lemma']=name+f'.certificate_{j}';route=r['route'];s+=f"/-- Local scalar projection: instance {r['instance']}, statement {r['statement']}. -/\n"
   if route=='fixed':
    n,spare=r['index'],r['spare'];s+=f'''def sourceState_{j} : IndexState := ⟨{n},{r['length']}⟩
theorem certificate_{j} {{α : Type}} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_{j}) ∧
      branch (indexGuard sourceState_{j}) normal first = branch (indexGuard sourceState_{j}) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate {n} {spare} normal first second
'''
   else:
    limit,slack=r['limit'],r['slack'];ns='PV_B3P_RangeEvents578227'if route=='range'else'PV_B3P_DominatedEvents578227';args=f'handler ⟨start,{limit}#usize⟩ {slack} effects'if route=='range'else f'{limit} {slack} index effects';params='(handler : Str → Result Never) (start : Usize)'if route=='range'else'(index : Nat)'
    s+=f'''def sourceState_{j} {params} (effects : List (Result Unit)) : Result (Option IndexState) :=
  {ns}.sourceEvent {args}
theorem certificate_{j} {{α : Type}} {params} (effects : List (Result Unit))
    (observed : IndexState) (ran : {ns}.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
'''
   s+=f'#print axioms certificate_{j}\n'
  outputs[D/'lean'/(name+'.lean')]=s+'end '+name+'\n'
 meta=dict(rows=rows,count=len(rows),chunks=chunks,source_frames=sources,named_const_bindings=bindings,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 scalar projection normalization, then existing kernel source-event guards; not complete source evaluator',native_pointer_validity='consumes shared pv-evhB4 owner relation when supplied; no separate owner relation constructed',whole_globals_association=False,whole_caller_association=False,premises_removed=[])
 outputs[R/'NORMALIZED-INDICES-D583.json']=json.dumps(meta,indent=2)+'\n'
 for p,s in outputs.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),chunks=chunks,controls=controls,check=a.check)))
if __name__=='__main__':main()
