"""Strict initializer source-event template binding; no native pointer credit.

The numeric guard fields are fresh private stack fields. The complete loop
prefix and continuing arm are checked, including arbitrary callback/branch,
UB-check branches, buffer write, and assert_inhabited. Residual/unwind exits
cannot return to an observed instruction. The retained pointer-realization
obligation is NOT discharged by this projection.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()

def compact(x):
 if isinstance(x,dict):return {k:compact(v) for k,v in x.items() if k not in ['ty','span','comments_before','generics']}
 if isinstance(x,list):return [compact(v)for v in x]
 return x

def find(x,n):
 if isinstance(x,dict):
  if x.get('id')==n and 'kind'in x:return x
  for v in x.values():
   if (r:=find(v,n))is not None:return r
 elif isinstance(x,list):
  for v in x:
   if (r:=find(v,n))is not None:return r

def nodes(x):
 if isinstance(x,dict):
  if 'id'in x and 'kind'in x and 'span'in x:yield x
  for v in x.values():yield from nodes(v)
 elif isinstance(x,list):
  for v in x:yield from nodes(v)

def local(p):return p=={'kind':{'Local':3}}
def certificate(f,template):
 # Exact whole-body template: no extra operation can be silently skipped.
 assert compact(f['body'])==template['source_body']
 # Fresh guard storage, exact aggregate count=0 and buffer handle from input1.
 init=find(f['body'],24717)['kind']['Assign'];assert init[0]['kind']=={'Local':3}
 fields=init[1]['Aggregate'][1]
 assert fields[0]['Copy']['kind']=={'Local':1}
 assert fields[1]['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','0']
 allnodes=list(nodes(f['body']))
 # No reference/raw pointer to the private stack guard or either of its fields
 # exists in this body. Copies of its buffer REFERENCE give access to the
 # buffer pointee, not to the stack field holding the reference or metadata.
 for n in allnodes:
  k=n['kind']
  if isinstance(k,dict)and 'Assign'in k:
   dest,rhs=k['Assign']
   for tag in ['Ref','RawPtr']:
    if tag in rhs:
     assert rhs[tag]['place']['kind'] in [{'Local':2},{'Projection':[find(f['body'],30819)['kind']['Assign'][1]['Ref']['place']['kind']['Projection'][0],'Deref']},{'Projection':[find(f['body'],24933)['kind']['Assign'][1]['RawPtr']['place']['kind']['Projection'][0],'Deref']}]
 # Loop test and reads are checked at their precise positions in the template.
 assert find(f['body'],24724)['kind']['Assign'][1]['BinaryOp'][0]=='Lt'
 assert find(f['body'],24985)['kind']['Switch']['If'][0]['Move']['kind']=={'Local':4}
 # The only writes to the private guard are constructor and post-event commit.
 private_writes=[]
 def root(p):
  k=p['kind']
  return k['Local']if 'Local'in k else root(k['Projection'][0])if 'Projection'in k else None
 for n in allnodes:
  k=n['kind']
  if isinstance(k,dict)and 'Assign'in k and root(k['Assign'][0])==3:private_writes.append(n['id'])
 assert private_writes==[24717,24979]
 # Every unwind block terminates; none can resume the continuing arm.
 unwind=[]
 def scan(x):
  if isinstance(x,dict):
   if x.get('on_unwind'):
    b=x['on_unwind']['statements'];last=b[-1]['kind'];assert last=='UnwindResume'or 'Abort'in last
    assert not {n['id']for n in nodes(x['on_unwind'])}&{24928,30822,24973}
    unwind.append(b[-1]['id'])
   for v in x.values():scan(v)
  elif isinstance(x,list):
   for v in x:scan(v)
 scan(f['body'])
 return dict(private_writes=private_writes,private_guard_address_never_exposed=True,terminal_unwind_blocks=unwind)

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];f=next(x for x in ll['fun_decls']if x and x['def_id']==370)
 template=json.loads((R/'INITIALIZER-TEMPLATE-D578.json').read_text());frame=certificate(f,template)
 controls={}
 def assign_rhs(n,k):return lambda x:find(x['body'],n)['kind']['Assign'].__setitem__(1,k)
 edits={
  'nonstrict_loop_test':lambda x:find(x['body'],24724)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,'Le'),
  'clobbered_counter_before_call':assign_rhs(24734,{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','999']}}}}},'Yes']}),
  'changed_buffer_metadata':assign_rhs(24723,{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','0']}}}}},'Yes']}),
  'guard_borrow_escape':lambda x:find(x['body'],24731)['kind']['Assign'][1]['Ref'].__setitem__('place',{'kind':{'Local':3}}),
  'changed_pointer_write':lambda x:find(x['body'],24943)['kind']['Assign'].__setitem__(0,{'kind':{'Local':3}}),
  'missing_inhabited_call':lambda x:find(x['body'],24956).__setitem__('kind','Nop'),
  'unwind_reentry':lambda x:find(x['body'],24927).__setitem__('kind',{'Continue':0}),
 }
 for name,edit in edits.items():
  changed=copy.deepcopy(f);edit(changed)
  try:certificate(changed,template)
  except (AssertionError,KeyError,TypeError):controls[name]='rejected'
  else:raise AssertionError(name)
 graph=json.loads((I/'direct3-instantiated-callcone.json').read_text());instances=[(k,v)for k,v in graph['instances'].items()if v['id']==370];assert len(instances)==16
 rows=[];s='import PV_B3P_InitializerEvents578227\nnamespace PV_B3P_InitializerFamily578227\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227\nset_option autoImplicit false\n'
 for j,(inst,v)in enumerate(instances):
  for statement,site,kind in [(24928,'indexPrecondition','index'),(30822,'index','index'),(24973,'addPrecondition','add')]:
   lemma=f'certificate_{j}_{statement}';rows.append(dict(instance=inst,statement=statement,environment=v['environment'],source_site=site,kind=kind,lemma='PV_B3P_InitializerFamily578227.'+lemma))
   guard='indexGuard observed'if kind=='index'else'arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))'
   apply=f'event_index_certificate .{site}'if kind=='index'else'event_add_certificate'
   s+=f'''/-- Actual LLBC instance {inst}, source instruction {statement}. -/
def sourceState_{j}_{statement} {{α β γ : Type}} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .{site} count length effects
theorem {lemma} {{α β γ δ : Type}} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_{j}_{statement} count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic ({guard}) ∧
      branch ({guard}) normal first = branch ({guard}) normal second :=
  {apply} count length effects observed ran normal first second
#print axioms {lemma}
'''
 s+='end PV_B3P_InitializerFamily578227\n'
 meta=dict(llbc_sha256=sha(raw),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),template_sha256=sha((R/'INITIALIZER-TEMPLATE-D578.json').read_bytes()),core_sha256=sha((D/'lean/PV_B3P_InitializerEvents578227.lean').read_bytes()),rows=rows,count=len(rows),frame=frame,negative_controls=controls,evidence_class='script-checked own-1 private scalar projection plus Lean prefix-event guard proof',source_program_binding=template['mapping'],native_pointer_validity=False,borrow_restoration=False,partial_initialization_and_drop=False,whole_caller_association=False,deployed_wrapper_discharged=False,premises_removed=[])
 for p,t in {D/'lean/PV_B3P_InitializerFamily578227.lean':s,R/'INITIALIZER-SOURCE-D578.json':json.dumps(meta,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(source_certificates=len(rows),negative_controls=controls,check=a.check)))
if __name__=='__main__':main()
