"""Conservative local constant propagation for actual fixed-array index states.
No loop invariant, callee effect, pointer validity or successful Result is
assumed. Calls/drops/unknown control kill all facts; projection writes do too.
Only scalar literal/copy assignments are reflected. No arithmetic is guessed.
"""
from pathlib import Path
import argparse,collections,hashlib,json,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
def literal(v):
 scalar=v.get('kind',{}).get('Literal',{}).get('Scalar',{}).get('Unsigned')
 return int(scalar[1]) if scalar and scalar[0]=='Usize' else None

def collect(body):
 rows=[]
 def operand(op,known):
  if 'Const'in op:
   n=literal(op['Const']);return (n,[])if n is not None else None
  for tag in ('Copy','Move'):
   if tag in op:return known.get(op[tag]['kind'].get('Local'))
 def walk(v):
  if isinstance(v,list):
   for x in v:walk(x)
  elif isinstance(v,dict):
   if 'statements'in v:block(v)
   else:
    for x in v.values():walk(x)
 def block(b):
  known={}
  for st in b['statements']:
   k=st['kind']
   if not isinstance(k,dict):known.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];slot=dest['kind'].get('Local')
    if slot is None:known.clear();continue
    # Evaluate before overwriting, so self-copy is represented faithfully.
    value=operand(rhs['Use'][0],known)if 'Use'in rhs else None
    if 'Use'in rhs and 'Move'in rhs['Use'][0]:known.pop(rhs['Use'][0]['Move']['kind'].get('Local'),None)
    known.pop(slot,None)
    if value is not None:known[slot]=(value[0],value[1]+[st])
   elif 'StorageDead'in k or 'StorageLive'in k:
    known.pop(next(iter(k.values())),None)
   elif 'Call'in k:
    call=k['Call']['call'];fun=call['func'].get('Regular',{});builtin=fun.get('kind',{}).get('Fun',{}).get('Builtin',{});idx=builtin.get('Index',{})if isinstance(builtin,dict)else {}
    if idx.get('is_array')is True and idx.get('is_range')is False:
     value=operand(call['args'][-1],known);cs=fun.get('generics',{}).get('const_generics',[]);length=literal(cs[0])if len(cs)==1 else None
     if value is not None and length is not None:
      n,derivation=value
      # A source counterexample blocks this item instead of hiding it.
      assert n<length,('fixed index out of bounds',st['id'],n,length)
      rows.append(dict(statement=st['id'],index=n,length=length,spare=length-n-1,derivation=derivation,source_call=dict(id=st['id'],span=st.get('span'),kind={'Call':{'call':call}})))
    known.clear();walk(k['Call'].get('on_unwind'))
   else:known.clear();walk(k)
 walk(body);return rows

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());inventory=json.loads((R/'FORMATTING-EVENTS-D569.json').read_text())['events'];keys={(e['instance'],e['statement'])for e in inventory if e['category'].startswith('builtin index')};rows=[];byfun={}
 for inst,v in g['instances'].items():
  fid=v['id']
  if fid not in byfun:byfun[fid]=collect(fs[fid]['body'])if fs[fid].get('body')else []
  for row in byfun[fid]:
   assert (inst,row['statement'])in keys
   rows.append(dict(instance=inst,environment=v['environment'],**row))
 assert len({(x['instance'],x['statement'])for x in rows})==len(rows)
 # Matched controls use a real array call; calls, projection writes and scope
 # invalidation between definition and use must prevent propagation.
 source=rows[0]['source_call'];import copy
 call=copy.deepcopy(source);call['kind']['Call']['call']['args'][-1]={'Copy':{'kind':{'Local':999}}}
 assignment=dict(id=-1,kind={'Assign':[{'kind':{'Local':999}},{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','0']}}}}},'Yes']}]})
 def fixture(middle):return {'statements':[assignment,*middle,call]}
 assert len(collect(fixture([])))==1
 controls={}
 for name,middle in {'call':[{ 'id':-2,'kind':{'Call':{'call':{'func':{},'args':[]},'on_unwind':None}}}], 'drop':[{'id':-2,'kind':{'Drop':{}}}], 'projection_write':[{'id':-2,'kind':{'Assign':[{'kind':{'Projection':[]}},{}]}}], 'storage_dead':[{'id':-2,'kind':{'StorageDead':999}}], 'loop':[{'id':-2,'kind':{'Loop':{'statements':[]}}}]}.items():
  assert not collect(fixture(middle)),name
  controls[name]='no certificate emitted'
 outputs={};chunks=[]
 for offset in range(0,len(rows),32):
  part=rows[offset:offset+32];name=f'PV_B3P_FixedIndices572227_{offset//32:02d}';chunks.append(name)
  s='import PV_B3P_FixedIndex572227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227\nset_option autoImplicit false\n'
  for j,row in enumerate(part,offset):
   n,length,spare=row['index'],row['length'],row['spare'];row['lemma']=name+f'.certificate_{j}'
   s+=f'''/-- Actual source instance {row['instance']}, statement {row['statement']}. -/
def sourceState_{j} : IndexState := ⟨{n}, {length}⟩
theorem guard_{j} : indexGuard sourceState_{j} := fixed_guard {n} {spare}
theorem certificate_{j} {{α : Type}} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_{j}) ∧
      branch (indexGuard sourceState_{j}) normal first =
        branch (indexGuard sourceState_{j}) normal second :=
  fixed_certificate {n} {spare} normal first second
#print axioms guard_{j}
#print axioms certificate_{j}
'''
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),rows=rows,count=len(rows),chunks=chunks,negative_controls=controls,evidence_class='script-checked own-1 local constant/state reflection and generated Lean guard applications',source_state_scope='Each listed argument is fixed by same-block scalar literal/copy definitions; array length is the actual builtin const generic.',whole_source_cone_complete=False,pointer_borrow_validity=False,premises_removed=[])
 outputs[R/'FIXED-INDICES-D572.json']=json.dumps(meta,indent=2)+'\n'
 for p,s in outputs.items():
  if args.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(fixed_indices=len(rows),chunks=chunks,controls=controls,check=args.check)))
if __name__=='__main__':main()
