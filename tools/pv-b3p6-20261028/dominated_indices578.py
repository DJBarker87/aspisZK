"""Track strict upper bounds of immutable scalar snapshots in actual LLBC.

Only strict comparisons with literal Usize upper bounds are consumed. No
callee or iterator return-bound theorem is assumed. Loop entries reset all
facts. Copy/Move, destination, scope and address escape semantics match the
private constant pass. All joins retain only identical snapshots on every
branch. This pass cannot establish pointer validity or the endpoint dictionary.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from fixed_indices572 import literal
from frame_indices578 import root,dicts
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def collect(body):
 exposed={root(x[tag]['place'])for x in dicts(body)for tag in ('Ref','RawPtr')if tag in x and isinstance(x[tag],dict)and 'place'in x[tag]}
 rows=[]
 def block(b,values,bounds,scope):
  values=dict(values);bounds=dict(bounds)
  def op(o,sid):
   if 'Const'in o:
    n=literal(o['Const']);return ('literal',n)if n is not None else None
   for tag in ('Copy','Move'):
    if tag in o and 'Local'in o[tag]['kind']:
     slot=o[tag]['kind']['Local']
     if slot not in values:values[slot]=('snapshot',scope,sid,slot)
     return values[slot]
   return None
  def moves(x):
   for n in dicts(x):
    if 'Move'in n:values.pop(root(n['Move']),None)
  def effect():
   for slot in exposed:values.pop(slot,None)
  for st in b['statements']:
   sid=st['id'];k=st['kind']
   if not isinstance(k,dict):values.clear();bounds.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];slot=root(dest);v=op(rhs['Use'][0],sid)if 'Use'in rhs else None
    if 'BinaryOp'in rhs:
     operator,left,right=rhs['BinaryOp'];a,c=op(left,sid),op(right,sid)
     if operator=='Lt' and a is not None and c is not None and c[0]=='literal':v=('less',a,c[1],sid)
    moves(rhs);values.pop(slot,None)
    if 'Local'in dest['kind']:values[slot]=v if v is not None else('snapshot',scope,sid,slot)
    else:effect()
   elif 'StorageDead'in k or 'StorageLive'in k:values.pop(next(iter(k.values())),None)
   elif 'Call'in k:
    call=k['Call']['call'];fun=call['func'].get('Regular',{});builtin=fun.get('kind',{}).get('Fun',{}).get('Builtin',{});idx=builtin.get('Index',{})if isinstance(builtin,dict)else{}
    if idx.get('is_array')is True and idx.get('is_range')is False:
     index=op(call['args'][-1],sid);cs=fun.get('generics',{}).get('const_generics',[]);length=literal(cs[0])if len(cs)==1 else None
     if index in bounds and length is not None:
      limit,predicate,branch=bounds[index]
      if limit<=length:rows.append(dict(statement=sid,index_snapshot=index,limit=limit,length=length,slack=length-limit,predicate_statement=predicate,dominating_branch=branch,source_call=st))
    moves(call['args']);values.pop(root(call.get('dest',{})),None);effect()
    if k['Call'].get('on_unwind'):block(k['Call']['on_unwind'],values,bounds,scope)
   elif 'Drop'in k:
    values.pop(root(k['Drop']['place']),None);effect()
    if k['Drop'].get('on_unwind'):block(k['Drop']['on_unwind'],values,bounds,scope)
   elif 'Assert'in k:moves(k['Assert'])
   elif 'Switch'in k:
    tag,v=next(iter(k['Switch'].items()));cond=op(v[0],sid)if tag=='If'else None;moves(v[0])
    if tag=='If':branches=v[1:]
    elif tag=='Match':branches=[b for _,b in v[1]]+([v[2]]if v[2]else[])
    elif tag=='SwitchInt':branches=[b for _,b in v[2]]+([v[3]]if v[3]else[])
    else:raise AssertionError(tag)
    exits=[]
    for i,child in enumerate(branches):
     child_bounds=dict(bounds)
     if tag=='If'and i==0 and cond is not None and cond[0]=='less':child_bounds[cond[1]]=(cond[2],cond[3],sid)
     exits.append(block(child,values,child_bounds,scope))
    values={slot:value for slot,value in exits[0][0].items()if all(e[0].get(slot)==value for e in exits[1:])}if exits else{}
    # Only the entry facts survive a join; refinements stay inside branches.
   elif 'Loop'in k:block(k['Loop'],{},{},sid);values.clear();bounds.clear()
   else:values.clear();bounds.clear()
  return values,bounds
 if body and 'Structured'in body:block(body['Structured']['body'],{},{},-1)
 elif body and 'statements'in body:block(body,{},{},-1)
 return rows

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text());allkeys={(r['instance'],r['statement'])for v in prior['groups'].values()for tag in ['remaining','certified']for r in v[tag]};already={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['certified']}
 for name in ['INITIALIZER-SOURCE-D578.json','FRAME-INDICES-D578.json','SLICE-SOURCE-D578.json']:already.update((r['instance'],r['statement'])for r in json.loads((R/name).read_text())['rows'])
 rows=[];byfun={}
 for inst,v in g['instances'].items():
  fid=v['id']
  if fid not in byfun:byfun[fid]=collect(fs[fid].get('body'))
  for row in byfun[fid]:
   if(inst,row['statement'])in already:continue
   assert(inst,row['statement'])in allkeys
   rows.append(dict(instance=inst,environment=v['environment'],function_id=fid,body_sha256=sha(json.dumps(fs[fid]['body'],sort_keys=True).encode()),**row))
 assert len(rows)==len({(r['instance'],r['statement'])for r in rows})
 # Exercise bound invalidation against actual builtin call syntax.
 call=copy.deepcopy(rows[0]['source_call']);call['kind']['Call']['call']['args'][-1]={'Copy':{'kind':{'Local':1}}}
 limit=min(rows[0]['length'],4)
 test=dict(id=-1,kind={'Assign':[{'kind':{'Local':3}},{'BinaryOp':['Lt',{'Copy':{'kind':{'Local':1}}},{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize',str(limit)]}}}}}]}]})
 def fixture(middle,negative=False):
  yes={'statements':[*middle,call]};no={'statements':[]}
  return {'statements':[test,dict(id=-2,kind={'Switch':{'If':[{'Move':{'kind':{'Local':3}}},no if negative else yes,yes if negative else no]}})]}
 assert len(collect(fixture([])))==1
 controls={}
 edits={
  'destination_clobber':[dict(id=-3,kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':1}}}}})],
  'moved_snapshot':[dict(id=-3,kind={'Call':{'call':{'func':{},'args':[{'Move':{'kind':{'Local':1}}}],'dest':{'kind':{'Local':99}}}}})],
  'storage_dead':[dict(id=-3,kind={'StorageDead':1})],
  'overwritten_snapshot':[dict(id=-3,kind={'Assign':[{'kind':{'Local':1}},{'NullaryOp':['unknown',{}]}]})],
  'borrowed_snapshot_across_effect':[dict(id=-3,kind={'Assign':[{'kind':{'Local':98}},{'Ref':{'place':{'kind':{'Local':1}},'kind':'Mut'}}]}),dict(id=-4,kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':99}}}}})],
  'loop_boundary':[dict(id=-3,kind={'Loop':{'statements':[]}})],
 }
 for name,middle in edits.items():
  assert not collect(fixture(middle)),name
  controls[name]='no certificate emitted'
 assert not collect(fixture([],True));controls['opposite_branch']='no certificate emitted'
 changed=fixture([]);changed['statements'][0]['kind']['Assign'][1]['BinaryOp'][0]='Le'
 assert not collect(changed);controls['nonstrict_predicate']='no certificate emitted'
 outputs={};chunks=[]
 for offset in range(0,len(rows),24):
  part=rows[offset:offset+24];name=f'PV_B3P_DominatedIndices578227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_DominatedEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_DominatedEvents578227\nset_option autoImplicit false\n'
  for j,row in enumerate(part,offset):
   limit,slack=row['limit'],row['slack'];row['lemma']=name+f'.certificate_{j}'
   s+=f'''/-- Instance {row['instance']}, instruction {row['statement']}, strict test {row['predicate_statement']}. -/
def sourceState_{j} (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent {limit} {slack} index effects
theorem certificate_{j} {{α : Type}} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate {limit} {slack} index effects observed ran normal first second
#print axioms certificate_{j}
'''
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),rows=rows,count=len(rows),chunks=chunks,negative_controls=controls,evidence_class='script-checked own-1 private scalar strict-comparison dominance plus generated Lean event guards',native_pointer_validity=False,whole_caller_association=False,premises_removed=[])
 outputs[R/'DOMINATED-INDICES-D578.json']=json.dumps(meta,indent=2)+'\n'
 for p,s in outputs.items():
  if args.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),chunks=chunks,check=args.check)))
if __name__=='__main__':main()
