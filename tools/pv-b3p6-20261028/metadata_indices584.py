"""Bind loop indices to caller-fixed immutable slice metadata, including native
slice index scalar guards. Element memory/restoration stays a separate obligation.
"""
from pathlib import Path
import json,lzma,hashlib,argparse,copy
from source_normalize584 import normalize
from metadata_source580 import certify
from flow_collect583 import collect
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());programs,coercions=certify(fs,json.loads((R/'METADATA-TEMPLATE-D580.json').read_text()));rows=[];frames=[]
 expected={224:2,241:6}
 for fid,params in [(224,{1:7,2:7}),(241,{1:4})]:
  incoming=[e for e in g['edges']if e['callee_id']==fid];assert len(incoming)==expected[fid]
  assert all(int(e['caller'].split(':')[0])==(50 if fid==224 else 59)for e in incoming)
  body,changes=normalize(fs[fid]['body'],{},params)
  inst=next(k for k,v in g['instances'].items()if v['id']==fid)
  for r in collect(body):rows.append(dict(instance=inst,function_id=fid,**r))
  frames.append(dict(instance=inst,parameters=params,incoming=incoming,source_sha256=sha(json.dumps(fs[fid]['body'],sort_keys=True).encode()),normalizations=changes))
 controls={};body=fs[241]['body']
 for label,k in {
  'fat_reference_reassigned':{'Assign':[{'kind':{'Local':1}},{'Use':[{'Const':{}},'Yes']}]},
  'fat_reference_address_exposed':{'Assign':[{'kind':{'Local':999}},{'Ref':{'place':{'kind':{'Local':1}},'kind':'Mut'}}]},
  'fat_reference_moved':{'Call':{'call':{'func':{},'args':[{'Move':{'kind':{'Local':1}}}],'dest':{'kind':{'Local':999}}}}},
  'fat_reference_lifetime_recreated':{'StorageLive':1},
 }.items():
  changed=copy.deepcopy(body);changed['Structured']['body']['statements'].insert(1,dict(id=-1,kind=k))
  try:normalize(changed,{}, {1:4})
  except AssertionError:controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_MetadataIndices584227';s='import PV_B3P_DominatedEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';n,slack=r['limit'],r['slack']
  s+=f'''/-- Instance {r['instance']}, statement {r['statement']}; all incoming metadata is bound. -/
def sourceState_{j} (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent {n} {slack} index effects
theorem certificate_{j} {{α : Type}} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate {n} {slack} index effects observed ran normal first second
#print axioms certificate_{j}
'''
 outputs={D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'METADATA-INDICES-D584.json':json.dumps(dict(rows=rows,count=len(rows),chunks=[name],frames=frames,caller_bindings='METADATA-SOURCE-D580.json; checked again over complete caller bodies',llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 scalar metadata projections and source continuing guards plus generated Lean event certificates',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[]),indent=2)+'\n'}
 for p,s in outputs.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),controls=controls,check=a.check)))
if __name__=='__main__':main()
