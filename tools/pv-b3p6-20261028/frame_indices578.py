"""Private scalar constant frames across source effects.

A local scalar is retained across a call only if NO Ref/RawPtr rooted in that
local occurs anywhere in the function. Calls kill destinations and all moved
arguments. Scope changes kill their slots. Unknown control resets facts;
branch entry inherits facts, branch joins reset them, loop entry resets them.
No claim about pointer validity or caller composition follows.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
def root(p):
 k=p.get('kind',{})
 if 'Local'in k:return k['Local']
 if 'Projection'in k:return root(k['Projection'][0])
 return None

def dicts(x):
 if isinstance(x,dict):
  yield x
  for v in x.values():yield from dicts(v)
 elif isinstance(x,list):
  for v in x:yield from dicts(v)

def collect(body):
 exposed=set()
 for x in dicts(body):
  for tag in ('Ref','RawPtr'):
   if tag in x and isinstance(x[tag],dict)and 'place'in x[tag]:exposed.add(root(x[tag]['place']))
 rows=[]
 def op(o,facts):
  if 'Const'in o:
   n=literal(o['Const']);return(n,[])if n is not None else None
  for tag in ('Copy','Move'):
   if tag in o and 'Local'in o[tag]['kind']:return facts.get(o[tag]['kind']['Local'])
 def moves(x,facts):
  for n in dicts(x):
   if 'Move'in n:facts.pop(root(n['Move']),None)
 def block(b,incoming):
  facts={k:v for k,v in incoming.items()if k not in exposed}
  for st in b['statements']:
   k=st['kind']
   if not isinstance(k,dict):facts.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];slot=root(dest);value=op(rhs['Use'][0],facts)if 'Use'in rhs else None
    moves(rhs,facts)
    facts.pop(slot,None)
    if 'Local'in dest['kind']and slot not in exposed and value is not None:facts[slot]=(value[0],value[1]+[st])
   elif 'StorageDead'in k or 'StorageLive'in k:facts.pop(next(iter(k.values())),None)
   elif 'Call'in k:
    call=k['Call']['call'];fun=call['func'].get('Regular',{});builtin=fun.get('kind',{}).get('Fun',{}).get('Builtin',{});idx=builtin.get('Index',{})if isinstance(builtin,dict)else{}
    if idx.get('is_array')is True and idx.get('is_range')is False:
     value=op(call['args'][-1],facts);cs=fun.get('generics',{}).get('const_generics',[]);length=literal(cs[0])if len(cs)==1 else None
     if value is not None and length is not None:
      n,derivation=value;assert n<length,('source fixed-index counterexample',st['id'],n,length)
      rows.append(dict(statement=st['id'],index=n,length=length,spare=length-n-1,derivation=derivation,source_call=st))
    moves(call['args'],facts);facts.pop(root(call.get('dest',{})),None)
    if k['Call'].get('on_unwind'):block(k['Call']['on_unwind'],facts)
   elif 'Drop'in k:
    facts.pop(root(k['Drop']['place']),None)
    if k['Drop'].get('on_unwind'):block(k['Drop']['on_unwind'],facts)
   elif 'Assert'in k:
    moves(k['Assert'],facts)
   elif 'Switch'in k:
    tag,v=next(iter(k['Switch'].items()));moves(v[0],facts)
    if tag=='If':branches=v[1:]
    elif tag=='Match':branches=[b for _,b in v[1]]+([v[2]]if v[2]else[])
    elif tag=='SwitchInt':branches=[b for _,b in v[2]]+([v[3]]if v[3]else[])
    else:raise AssertionError(tag)
    for child in branches:block(child,facts)
    facts.clear()
   elif 'Loop'in k:block(k['Loop'],{});facts.clear()
   else:facts.clear()
 if body and 'Structured'in body:block(body['Structured']['body'],{})
 elif body and 'statements'in body:block(body,{})
 return rows,sorted(n for n in exposed if n is not None)

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};graph=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text());already={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['certified']};rows=[];byfun={}
 keys={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['remaining']}
 for inst,v in graph['instances'].items():
  fid=v['id']
  if fid not in byfun:byfun[fid]=collect(fs[fid].get('body'))
  found,exposed=byfun[fid]
  for row in found:
   if(inst,row['statement'])in already:continue
   assert(inst,row['statement'])in keys,(inst,row['statement'])
   rows.append(dict(instance=inst,environment=v['environment'],function_id=fid,body_sha256=sha(json.dumps(fs[fid]['body'],sort_keys=True).encode()),address_exposed_locals=exposed,**row))
 assert len(rows)==len({(r['instance'],r['statement'])for r in rows})
 # Matched controls exercise the frame rule, not merely the literal bound.
 fixture_call=copy.deepcopy(rows[0]['source_call'])
 fixture_call['kind']['Call']['call']['args'][-1]={'Copy':{'kind':{'Local':999}}}
 assignment=dict(id=-1,kind={'Assign':[{'kind':{'Local':999}},{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','0']}}}}},'Yes']}]})
 call=dict(id=-2,kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':998}}}}})
 def fixture(middle):return {'statements':[assignment,*middle,fixture_call]}
 assert len(collect(fixture([call]))[0])==1
 controls={}
 edits={
  'call_destination_clobber':[dict(id=-2,kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':999}}}}})],
  'move_to_callee':[dict(id=-2,kind={'Call':{'call':{'func':{},'args':[{'Move':{'kind':{'Local':999}}}],'dest':{'kind':{'Local':998}}}}})],
  'address_escape':[dict(id=-2,kind={'Assign':[{'kind':{'Local':998}},{'Ref':{'place':{'kind':{'Local':999}},'kind':'Mut'}}]})],
  'raw_address_escape':[dict(id=-2,kind={'Assign':[{'kind':{'Local':998}},{'RawPtr':{'place':{'kind':{'Local':999}},'kind':'Mut'}}]})],
  'storage_dead':[dict(id=-2,kind={'StorageDead':999})],
  'overwrite':[dict(id=-2,kind={'Assign':[{'kind':{'Local':999}},{'NullaryOp':['unknown',{}]}]})],
  'loop_boundary':[dict(id=-2,kind={'Loop':{'statements':[]}})],
  'branch_join':[dict(id=-2,kind={'Switch':{'If':[{'Const':{}},{'statements':[]},{'statements':[]}]}})],
 }
 for name,middle in edits.items():
  assert not collect(fixture(middle))[0],name
  controls[name]='no certificate emitted'
 # A borrow appearing AFTER the use also prohibits assuming stack privacy.
 trailing=fixture([]);trailing['statements']+=edits['address_escape']
 assert not collect(trailing)[0];controls['later_address_escape']='no certificate emitted'
 outputs={};chunks=[]
 for offset in range(0,len(rows),24):
  part=rows[offset:offset+24];name=f'PV_B3P_FrameIndices578227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_FixedIndex572227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227\nset_option autoImplicit false\n'
  for j,row in enumerate(part,offset):
   n,length,spare=row['index'],row['length'],row['spare'];row['lemma']=name+f'.certificate_{j}'
   s+=f'''/-- Actual source instance {row['instance']}, instruction {row['statement']}. -/
def sourceState_{j} : IndexState := ⟨{n}, {length}⟩
theorem certificate_{j} {{α : Type}} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_{j}) ∧
      branch (indexGuard sourceState_{j}) normal first =
        branch (indexGuard sourceState_{j}) normal second :=
  fixed_certificate {n} {spare} normal first second
#print axioms certificate_{j}
'''
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),rows=rows,count=len(rows),chunks=chunks,negative_controls=controls,evidence_class='script-checked own-1 private scalar constant/state reflection and generated Lean bound applications',source_state_scope='Unexposed scalar locals survive calls and unrelated writes. Moves, destinations and StorageLive/Dead invalidate. Branch joins and loop entries reset.',whole_source_cone_complete=False,pointer_borrow_validity=False,premises_removed=[])
 outputs[R/'FRAME-INDICES-D578.json']=json.dumps(meta,indent=2)+'\n'
 for p,s in outputs.items():
  if args.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),chunks=chunks,check=args.check)))
if __name__=='__main__':main()
