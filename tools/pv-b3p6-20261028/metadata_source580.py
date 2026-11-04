"""Bind equal-length dot and <=4 pack assertions to actual array metadata.
Full local prefixes lower to an executable store interpreter. All captured
incoming calls use ArrayToSliceShared at literal lengths7/7 and4 respectively.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma,re
from initializer_source578 import compact,find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def local(p):assert 'Local'in p['kind'];return p['kind']['Local']
def operand(o):return local(next(iter(o.values())))
def prefix(f,stop):
 b=f['body']['Structured']['body']['statements'];cut=next(i for i,s in enumerate(b)if s['id']==stop);return b[:cut]
def lower(st):
 k=st['kind'];assert isinstance(k,dict)
 if 'StorageLive'in k or 'StorageDead'in k:return('kill',next(iter(k.values())))
 if 'Call'in k:
  c=k['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':23}and len(c['args'])==1
  return('lenCall',local(c['dest']),operand(c['args'][0]))
 dest,rhs=k['Assign'];d=local(dest)
 if 'Ref'in rhs:
  p=rhs['Ref']['place'];assert rhs['Ref']['kind']=='Shared'
  if 'Local'in p['kind']:return('address',d,local(p))
  p,proj=p['kind']['Projection'];assert proj=='Deref'
  return('copy',d,local(p))
 if 'Aggregate'in rhs:
  tag,args=rhs['Aggregate'];assert tag['Adt'][0]['id']=='Tuple'and len(args)==2
  return('pairMove',d,operand(args[0]),operand(args[1]))
 if 'Use'in rhs:
  op=rhs['Use'][0];p,projection=next(iter(op.values()))['kind']['Projection']
  if projection=='Deref':return('load',d,local(p))
  field=projection['Field'];assert field[0]=={'Tuple':2}and field[1]in [0,1]
  return('field',d,local(p),'true'if field[1]else'false')
 op,left,right=rhs['BinaryOp']
 if op=='Eq':return('equalMove',d,operand(left),operand(right))
 assert op=='Le'and right['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','4']
 return('leMove',d,operand(left),4)
def certify(fs,t):
 dot=prefix(fs[224],13375);pack=prefix(fs[241],19252)
 assert compact(dot)==t['dot_prefix']and compact(pack)==t['pack_prefix']
 assert compact(fs[50]['body'])==t['caller50']and compact(fs[59]['body'])==t['caller59']
 leaf=compact(fs[23]['body']['Structured']['body']['statements'])
 assert leaf==[{'id':3195,'kind':{'StorageLive':0}},{'id':3196,'kind':{'Assign':[{'kind':{'Local':0}},{'Use':[{'Copy':{'kind':{'Projection':[{'kind':{'Local':1}},'PtrMetadata']}}},'No']}]}},{'id':3197,'kind':{'StorageDead':1}},{'id':3198,'kind':'Return'}]
 programs=dict(equality=[lower(s)for s in dot],pack=[lower(s)for s in pack])
 # Pair literal lengths for both actual dot calls; complete source bodies
 # and prefixes prevent extra metadata writes from being silently skipped.
 coercions=[]
 for fid,sites,n in [(50,[4536,4543,4559,4566],7),(59,[7268],4)]:
  for sid in sites:
   c=find(fs[fid]['body'],sid)['kind']['Call']['call'];f=c['func']['Regular'];assert f['kind']['Fun']=={'Builtin':'ArrayToSliceShared'}
   cs=f['generics']['const_generics'];assert len(cs)==1 and cs[0]['kind']['Literal']['Scalar']['Unsigned']==['Usize',str(n)]
   coercions.append(dict(function=fid,statement=sid,length=n,dest=local(c['dest'])))
 for sid,args in [(4548,[11,14]),(4571,[18,21]),(7282,[44])]:
  fid=59 if sid==7282 else 50;c=find(fs[fid]['body'],sid)['kind']['Call']['call'];target=241 if fid==59 else 224
  assert c['func']['Regular']['kind']['Fun']=={'Regular':target}and[operand(x)for x in c['args']]==args
  # Between the checked coercion and consuming call there are only scope
  # actions and the OTHER coercion/ref preparations; no destination rewrite.
 return programs,coercions

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};t=json.loads((R/'METADATA-TEMPLATE-D580.json').read_text());programs,coercions=certify(fs,t)
 core=(D/'lean/PV_B3P_MetadataSource580227.lean').read_text()
 for key,defname in [('equality','equalityProgram'),('pack','packProgram')]:
  actual=re.search(r'def '+defname+r'.*?: List Instr :=\s*(\[.*?\])',core,re.S)[1]
  rendered='['+', '.join('.'+op[0]+' '+' '.join(map(str,op[1:]))for op in programs[key])+']'
  if key=='pack':rendered=rendered.replace('.leMove 2 3 4','.leMove 2 3 bound')
  assert re.sub(r'\s+','',actual)==re.sub(r'\s+','',rendered),(key,rendered)
 g=json.loads((I/'direct3-instantiated-callcone.json').read_text());incoming={fid:[e for e in g['edges']if e['callee_id']==fid]for fid in [224,241]}
 assert len(incoming[224])==2 and all(e['caller'].startswith('50:')for e in incoming[224])
 assert len(incoming[241])==6 and all(e['caller'].startswith('59:')for e in incoming[241])
 controls={}
 edits={
  'different_dot_lengths':lambda f:find(f[50]['body'],4543)['kind']['Call']['call']['func']['Regular']['generics']['const_generics'][0]['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'6'),
  'oversize_pack_input':lambda f:find(f[59]['body'],7268)['kind']['Call']['call']['func']['Regular']['generics']['const_generics'][0]['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'5'),
  'different_len_source':lambda f:find(f[23]['body'],3196)['kind']['Assign'][1]['Use'][0]['Copy']['kind'].__setitem__('Local',2),
  'clobbered_length_comparison':lambda f:find(f[224]['body'],13315)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,'Ne'),
  'different_packed_bound':lambda f:find(f[241]['body'],19250)['kind']['Assign'][1]['BinaryOp'][2]['Const']['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'3'),
 }
 for name,edit in edits.items():
  changed=copy.deepcopy(fs);edit(changed)
  try:certify(changed,t)
  except(AssertionError,KeyError):controls[name]='rejected'
  else:raise AssertionError(name)
 s='''import PV_B3P_MetadataSource580227
namespace PV_B3P_MetadataFamily580227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_MetadataSource580227
set_option autoImplicit false
''';rows=[]
 for fid,sid,n,sites,kind in [(224,13374,7,2,'equality'),(241,19252,4,6,'pack')]:
  name=f'certificate_{fid}';inst=next(k for k,v in g['instances'].items()if v['id']==fid);rows.append(dict(instance=inst,statement=sid,lemma='PV_B3P_MetadataFamily580227.'+name,incoming=incoming[fid],length=n))
  state=f'equalityState prior {n} {n}'if kind=='equality'else f'packState prior {n} {n}';slot=12 if kind=='equality'else 2;app=f'equality_certificate prior {n}'if kind=='equality'else f'pack_certificate prior {n} 0'
  s+=f'''/-- Every one of the{sites} captured incoming calls has this metadata state. -/
def sourceState_{fid} (_caller : Fin {sites}) (prior : Store) : Store := {state}
theorem {name} {{α : Type}} (caller : Fin {sites}) (prior : Store) (normal first second : Result α) :
    ¬ diagnostic (condition (sourceState_{fid} caller prior) {slot} = true) ∧
      branch (condition (sourceState_{fid} caller prior) {slot} = true) normal first =
        branch (condition (sourceState_{fid} caller prior) {slot} = true) normal second :=
  {app} normal first second
#print axioms {name}
'''
 s+='end PV_B3P_MetadataFamily580227\n'
 meta=dict(llbc_sha256=sha(raw),rows=rows,count=2,template_sha256=sha((R/'METADATA-TEMPLATE-D580.json').read_bytes()),programs=programs,source_coercions=coercions,negative_controls=controls,evidence_class='script-checked own-1 actual array-to-slice metadata/caller frames and complete local store prefix with Lean assertion guards',native_pointer_validity=False,bytes_or_arithmetic_semantics_assumed=False,whole_caller_association=False,premises_removed=[])
 for out,text in {D/'lean/PV_B3P_MetadataFamily580227.lean':s,R/'METADATA-SOURCE-D580.json':json.dumps(meta,indent=2)+'\n'}.items():
  if a.check:assert out.read_text()==text,out
  else:out.write_text(text)
 print(json.dumps(dict(local_checks=2,captured_inputs=8,controls=controls,check=a.check)))
if __name__=='__main__':main()
