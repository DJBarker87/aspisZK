"""Complete literal COPY_LINKS/COPY_PATTERNS scalar-domain projections.
Each small literal is given a named Fin theorem; no full table reduction.
"""
from pathlib import Path
import json,lzma,hashlib,copy,argparse
from literal_tables592 import initialize
from initializer_source578 import compact,find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def read(st):return compact(st['kind']['Assign'][1]['Use'][0])
def certify(ll,g,t):
 fs={f['def_id']:f for f in ll['fun_decls']if f}
 for fid in [21,70,245,252,253]:assert compact(fs[fid]['body'])==t[str(fid)]
 for gid,fid in[(11,247),(58,462)]:
  gl=next(q for q in ll['global_decls']if q and q['def_id']==gid);assert gl['global_kind']=='NamedConst'and compact(gl['value'])=={'kind':{'Call':[{'kind':{'Fun':{'Regular':fid}}},[]]}}
 links,le=initialize(fs[247]);patterns,pe=initialize(fs[462]);assert len(links['fields'])==136 and len(patterns['fields'])==14
 slots=[];pats=[];columns=[]
 for link in links['fields']:
  assert link['tag']['Adt'][0]['id']=={'Adt':33}and len(link['fields'])==5
  ends=link['fields'][3:];assert all(e['tag']['Adt'][0]['id']=={'Adt':34}and len(e['fields'])==3 for e in ends)
  slots.append([e['fields'][1]for e in ends]);pats.append([e['fields'][2]for e in ends])
 for pat in patterns['fields']:
  assert pat['tag']['Adt'][0]['id']=={'Adt':98}and len(pat['fields'])==3
  columns.append(pat['fields'][1]['fields']);assert len(columns[-1])==16
 assert all(0<=v<2 for r in slots for v in r)and all(0<=v<14 for r in pats for v in r)and all(0<=v<16 for r in columns for v in r)
 # Exact source table -> copied link -> endpoint field -> call argument routes.
 assert read(find(fs[21]['body'],2952))=={'Copy':{'kind':{'Global':{'id':11}}}}
 assert read(find(fs[21]['body'],2957))=={'Copy':{'kind':{'Projection':[{'kind':{'Local':58}},'Deref']}}}
 for sid,field,local,call in[(2992,3,31,3013),(3035,4,42,3056)]:
  assert read(find(fs[21]['body'],sid))=={'Copy':{'kind':{'Projection':[{'kind':{'Local':19}},{'Field':[{'Adt':[33,None]},field]}]}}}
  c=compact(find(fs[21]['body'],call)['kind']['Call']['call']);assert c['func']['Regular']['kind']['Fun']=={'Regular':70}and c['args'][2]=={'Move':{'kind':{'Local':local}}}
 assert len([e for e in g['edges']if e['callee_id']==70])==2
 # Exact deployed unsigned-to-usize casts, not a black-box helper result.
 for fid in[252,253]:
  ss=[q for q in fs[fid]['body']['Structured']['body']['statements']if isinstance(q['kind'],dict)and'Assign'in q['kind']];assert len(ss)==1
  rhs=ss[0]['kind']['Assign'][1];assert 'UnaryOp'in rhs and 'Cast'in rhs['UnaryOp'][0]
 return dict(slots=slots,patterns=pats,columns=columns),dict(link_initializer=247,link_events=le,pattern_initializer=462,pattern_events=pe,source_hashes={str(fid):sha(json.dumps(fs[fid]['body'],sort_keys=True).encode())for fid in[21,70,245,247,252,253,462]})
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'TABLE-TEMPLATE-D592.json').read_text());tables,binding=certify(ll,g,t);controls={}
 for fid,sid,label in[(21,2992,'endpoint_projection_changed'),(70,8350,'slot_read_changed'),(245,19899,'pattern_read_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid)
  # Template rejection covers every control/store/drop, not only selected steps.
  if sid==19899:sid=f['body']['Structured']['body']['statements'][0]['id']
  find(f['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_TableIndices592227';s='import PV_B3P_TableEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for table,bound in [('slots',2),('patterns',14),('columns',16)]:
  vals=sorted({v for r in tables[table]for v in r})
  for v in vals:s+=f'def {table}_{v} : Fin {bound} := ⟨{v},by decide⟩\n'
  s+=f'def source_{table} : List (List (Fin {bound})) := [\n  '+',\n  '.join('['+','.join(table+'_'+str(v)for v in r)+']'for r in tables[table])+']\n'
 rows=[]
 for fid,sid,table,bound in [(70,29689,'slots',2),(70,29694,'slots',2),(70,29699,'patterns',14),(70,29704,'slots',2),(70,29709,'slots',2),(245,30521,'columns',16)]:
  inst=next(k for k,v in g['instances'].items()if v['id']==fid);label=f'certificate_{fid}_{sid}';args=f'{bound} source_{table} row column effects';rows.append(dict(instance=inst,function_id=fid,statement=sid,lemma=name+'.'+label,table=table))
  s+=f'''/-- Exact immutable scalar table projection at {inst}:{sid}. -/
theorem {label} {{α : Type}} (row column : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_TableEvents592227.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_TableEvents592227.event_certificate {args} observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=rows,count=6,chunks=[name],tables=tables,binding=binding,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 complete immutable scalar table and caller/read/cast projections plus named kernel guards',validation_status='PREPARATION; focused compiles and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',native_global_initialization=False,native_borrow_restoration=False,whole_caller_association=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'TABLE-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(count=6,check=a.check,controls=controls)))
if __name__=='__main__':main()
