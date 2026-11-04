"""Source caller-loop tests through ArrayToSliceMut -> initializer -> wrap_mut_1
-> closure tuple forwarding. This binds only numeric callback-index observations.
"""
from pathlib import Path
import json,lzma,hashlib,argparse,copy
from initializer_source578 import compact,find,certificate
from callback_collect584 import collect
from frame_indices578 import dicts
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def source_chain(fs,t):
 for fid in [229,364]:assert compact(fs[fid]['body'])==t[str(fid)]
 certificate(fs[370],json.loads((R/'INITIALIZER-TEMPLATE-D578.json').read_text()))
 for sid,builtin in [(15441,'ArrayRepeat'),(15446,'ArrayToSliceMut')]:
  c=find(fs[229]['body'],sid)['kind']['Call']['call'];f=c['func']['Regular'];assert f['kind']['Fun']=={'Builtin':builtin}
  assert len(f['generics']['const_generics'])==1 and f['generics']['const_generics'][0]['kind']=={'Var':{'Free':0}}
 c=find(fs[229]['body'],15451)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':370}and compact(c['args'])==[{'Move':{'kind':{'Local':4}}},{'Move':{'kind':{'Local':1}}}]
 # Both tuple constructions pass OLD count, before the sole post-event commit.
 assert compact(find(fs[370]['body'],24735)['kind'])=={'Assign':[{'kind':{'Local':11}},{'Aggregate':[{'Adt':[{'id':'Tuple'},None,None]},[{'Move':{'kind':{'Local':12}}}]]}]}
 assert compact(find(fs[364]['body'],24616)['kind'])=={'Assign':[{'kind':{'Local':6}},{'Aggregate':[{'Adt':[{'id':'Tuple'},None,None]},[{'Copy':{'kind':{'Local':3}}}]]}]}

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'CALLBACK-TEMPLATE-D584.json').read_text());source_chain(fs,t);edges=g['edges'];rows=[];frames=[]
 x=json.loads((R/'SOURCE-COVERAGE-D580.json').read_text());remaining={(r['instance'],r['statement'])for v in x['groups'].values()for r in v['remaining']}
 for file in ['NORMALIZED-INDICES-D583','COMPUTED-INDICES-D583','METADATA-INDICES-D584']:remaining-={(r['instance'],r['statement'])for r in json.loads((R/(file+'.json')).read_text())['rows']}
 for fid in [199,428,432,504,506,508,524,536]:
  inst=next(k for k,v in g['instances'].items()if v['id']==fid);cur=inst;chain=[]
  for expected in [364,370,229]:
   incoming=[e for e in edges if e['callee']==cur];assert len(incoming)==1
   edge=incoming[0];cur=edge['caller'];assert g['instances'][cur]['id']==expected;chain.append(edge)
  cs=g['instances'][cur]['environment']['const_generics'];assert len(cs)==1;n=literal(cs[0]);assert n==4
  original=fs[fid]['body'];b=copy.deepcopy(original);extractions=[]
  assert all(x.get('index')!=777 for x in b['Structured']['locals']['locals'])
  for st in b['Structured']['body']['statements']:
   k=st['kind']
   if isinstance(k,dict)and'Assign'in k:
    dest,rhs=k['Assign']
    if 'Use'in rhs:
     o=compact(rhs['Use'][0]);place={'Projection':[{'kind':{'Local':2}},{'Field':[{'Tuple':1},0]}]}
     if any(o.get(tag,{}).get('kind')==place for tag in ['Copy','Move']):
      extractions.append(dict(statement=st['id'],source=copy.deepcopy(st)));rhs['Use'][0]={'Copy':{'kind':{'Local':777}}}
  assert len(extractions)==1
  # No prior address access to the tuple can change the scalar before extraction.
  first=extractions[0]['statement'];prefix=b['Structured']['body']['statements'];cut=next(i for i,q in enumerate(prefix)if q['id']==first)
  assert all('StorageLive'in q['kind']for q in prefix[:cut])
  mark=('callback',fid);source_rows=collect(b,initial=({777:mark},{mark:(n,24724,24985)}))
  accepted=[]
  for row in source_rows:
   if(inst,row['statement'])in remaining:
    assert row['index_snapshot']==mark;rows.append(dict(instance=inst,function_id=fid,**row));accepted.append(row['statement'])
  frames.append(dict(instance=inst,source_sha256=sha(json.dumps(original,sort_keys=True).encode()),actual_incoming_chain=chain,buffer_length=n,extractions=extractions,statements=accepted))
 controls={}
 for label,fid,sid in [('buffer_coercion_changed',229,15446),('callback_forwarding_changed',364,24616),('source_counter_changed',370,24734)]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:source_chain(changed,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_CallbackIndices584227';s='import PV_B3P_DominatedEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';n,slack=r['limit'],r['slack'];s+=f'''/-- Caller initializer test, two checked tuple forwards, source event {r['instance']}:{r['statement']}. -/
def sourceState_{j} (count : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent {n} {slack} count effects
theorem certificate_{j} {{α : Type}} (count : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} count effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate {n} {slack} count effects observed ran normal first second
#print axioms certificate_{j}
'''
 outputs={D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'CALLBACK-INDICES-D584.json':json.dumps(dict(rows=rows,count=len(rows),chunks=[name],source_frames=frames,initializer_binding='INITIALIZER-SOURCE-D578.json / full source template rechecked',templates='CALLBACK-TEMPLATE-D584.json',llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 actual caller scalar-test/metadata/tuple projections plus kernel guards; no assumed callback-index bound',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',mutable_capture_restoration=False,whole_caller_association=False,premises_removed=[]),indent=2)+'\n'}
 for p,s in outputs.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),source_chains=len(frames),controls=controls,check=a.check)))
if __name__=='__main__':main()
