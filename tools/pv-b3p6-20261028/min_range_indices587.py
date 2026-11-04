"""Bind source min-capped ranges to literal caller metadata.
Upper-bound discovery rewrites are explicitly abstractions, never body equality.
The emitted event retains the ACTUAL min and actual arbitrary range start.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from source_normalize584 import normalize
from metadata_source580 import certify
from range_caps587 import seeds
from flow_collect587 import collect
from initializer_source578 import find,compact
import re
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def parity():
 rows=[]
 for version in ['1.94.1','nightly-2026-06-01']:
  p=R/'std587-source'/version/'cmp.rs.xz';raw=lzma.decompress(p.read_bytes());s=raw.decode();a=s.index('fn min(self, other: Self)');b=s.index('{',a);end=s.index('\n    }',b)+6;body=s[b:end]
  assert tok(body)==tok('{ if other < self { other } else { self } }')
  rows.append(dict(version=version,source=str(p),sha256=sha(raw),body=body,body_sha256=sha(body.encode())))
 return rows

def binding(fs,g):
 t=json.loads((R/'MIN-RANGE-TEMPLATE-D587.json').read_text())
 for fid in [224,361]:assert compact(fs[fid]['body'])==t[str(fid)]
 programs,coercions=certify(fs,json.loads((R/'METADATA-TEMPLATE-D580.json').read_text()))
 incoming=[e for e in g['edges']if e['callee_id']==224];assert len(incoming)==2 and all(e['caller'].startswith('50:')for e in incoming)
 c=find(fs[361]['body'],24238)['kind']['Call']['call'];assert compact(c['args'])==[{'Move':{'kind':{'Local':1}}},{'Move':{'kind':{'Local':2}}}]
 assert c['func']['Regular']['kind']['Trait'][1]==2
 es=[e for e in g['edges']if e['caller'].startswith('361:')];assert len(es)==1 and es[0]['callee_id']==273
 b,changes=normalize(fs[224]['body'],{}, {1:7,2:7});c=find(b,13771)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':361}
 assert compact(c['args'])==[{'Move':{'kind':{'Local':82}}},{'Move':{'kind':{'Local':84}}}]
 assert compact(find(b,13728)['kind']['Assign'][1]['Use'][0])=={'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','7']}}}}}
 assert compact(find(b,13783)['kind']['Assign'][1]['Aggregate'][1])==[{'Move':{'kind':{'Local':89}}},{'Move':{'kind':{'Local':90}}}]
 assert compact(find(b,13782)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Local':81}}}
 original=copy.deepcopy(find(b,13771));dest=c['dest'];find(b,13771)['kind']={'Assign':[dest,{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','7']}}}}},'Yes']}]}
 find(b,13783)['kind']['Assign'][1]['Aggregate'][1][1]={'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','7']}}}}}
 sd,frames=seeds(b);assert any(v[1:]==(7,13878)for v in sd.values())
 rs,nested=collect(b,sd);rows=[r for r in rs if r['statement']in[30036,30041]];assert len(rows)==2 and all(r['predicate_statement']==13878 for r in rows)
 return rows,dict(incoming=incoming,metadata_normalizations=changes,min_source_call=original,min_dictionary_edge=es[0],range_frames=frames,nested_frames=nested,discovery_abstraction='replace min result by proven upper bound ONLY for range-end frame discovery; generated sourceEvent keeps actual min',body_sha256=sha(json.dumps(fs[224]['body'],sort_keys=True).encode()))
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());ps=parity();rows,frame=binding(fs,g);inst=next(k for k,v in g['instances'].items()if v['id']==224);controls={}
 for sid,label in [(13771,'wrong_min_helper'),(13782,'wrong_end_forward'),(13783,'wrong_range_constructor')]:
  changed=copy.deepcopy(fs);find(changed[224]['body'],sid)['kind']={'StorageDead':999}
  try:binding(changed,g)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_MinRangeIndices587227';s='import PV_B3P_MinRangeEvents587227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_MinRangeEvents587227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r.update(instance=inst,function_id=224,lemma=name+f'.certificate_{j}')
  s+=f'''/-- Source min/cursor/metadata projection at {inst}:{r['statement']}. -/
def sourceState_{j} (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent handler start candidate 7#usize 0 effects
theorem certificate_{j} {{α : Type}} (handler : Str → Result Never) (start candidate : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_{j} handler start candidate effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler start candidate 7#usize 0 effects observed ran normal first second
#print axioms certificate_{j}
'''
 out={D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'MIN-RANGE-INDICES-D587.json':json.dumps(dict(rows=rows,count=2,chunks=[name],source_frame=frame,source_parity=ps,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 min/range scalar and immutable caller metadata projection plus named kernel bounds',whole_caller_association=False,native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',step_by_reachability=False,premises_removed=[]),indent=2)+'\n'}
 for p,s in out.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=2,check=a.check,controls=controls)))
if __name__=='__main__':main()
