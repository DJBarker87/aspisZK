"""Bind helper318's scalar slice metadata to assertion319's actual input.
This is an own-1 control/metadata projection, with pointer realization separate.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy,re
from initializer_source578 import compact,find,nodes
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
def body(path,needle,contains=None):
 raw=lzma.decompress(path.read_bytes());s=raw.decode();candidates=[]
 for m in re.finditer(re.escape(needle),s):
  b=s.index('{',m.start());i=b+1;depth=1
  while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
  value=s[b:i]
  if contains is None or contains in value:candidates.append(value)
 assert len(candidates)==1,(path,needle,len(candidates))
 return dict(path=str(path),source_sha256=sha(raw),body=candidates[0],body_sha256=sha(candidates[0].encode()))
EXPECTED=[('array/mod.rs','fn index(&self, index: I)',None,'{ Index::index(self as &[T], index) }'),('slice/index.rs','fn index(&self, index: I)',None,'{ index.index(self) }'),('slice/index.rs','fn index(self, slice: &[T])','usize::checked_sub(self.end, self.start)','{ if let Some(new_len) = usize::checked_sub(self.end, self.start) && self.end <= slice.len() { unsafe { &*get_offset_len_noubcheck(slice, self.start, new_len) } } else { slice_index_fail(self.start, self.end, slice.len()) } }'),('slice/index.rs','fn get_offset_len_noubcheck',None,'{ let ptr = ptr as *const T; let ptr = unsafe { crate::intrinsics::offset(ptr, offset) }; crate::intrinsics::aggregate_raw_ptr(ptr, len) }')]
def parity():
 rows=[]
 for name,needle,contains,expected in EXPECTED:
  pair=[]
  for version in ['1.94.1','nightly-2026-06-01']:
   p=R/('std559-source'if name.startswith('array')else'std581-source')/version/(name+'.xz');b=body(p,needle,contains);assert tok(b['body'])==tok(expected),(name,version);pair.append(dict(version=version,**b))
  rows.append(dict(item=needle,source_pair=pair,body_tokens_identical=True))
 return rows

def certify(fs,g,t):
 assert compact(fs[199]['body'])==t['199'];assert compact(fs[319]['body'])==t['319']
 ins=[(k,v)for k,v in g['instances'].items()if v['id']==318];assert len(ins)==1;inst,info=ins[0];assert fs[318]['body']=='Opaque'
 env=info['environment'];assert literal(env['const_generics'][0])==16 and len(env['const_generics'])==1
 tr=env['trait_refs'][0]['kind']['TraitImpl'];assert tr['id']==77 and tr['generics']['trait_refs'][0]['kind']['TraitImpl']['id']==78
 for fid in [318,319]:
  incoming=[e for e in g['edges']if e['callee_id']==fid];assert len(incoming)==2 and all(e['caller'].startswith('199:')for e in incoming)
 bindings=[]
 for sid,pack,range_sid,add_sid,refs,slots in [(9614,9631,9599,9597,[9617,9618],[9,8,7]),(9665,9682,9650,9648,[9668,9669],[18,17,16])]:
  c=find(fs[199]['body'],sid)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':318}and c['dest']['kind']=={'Local':slots[0]}
  add=compact(find(fs[199]['body'],add_sid)['kind']['Assign'][1]['BinaryOp']);assert add[0]=={'Add':'Wrap'}and literal(add[2]['Const'])==4
  # Both operands are copies of the SAME private start scalar4.
  starts,ends,base=(12,13,14)if sid==9614 else(21,22,23)
  for copy_sid in ([9593,9596]if sid==9614 else[9644,9647]):
   assert compact(find(fs[199]['body'],copy_sid)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Local':4}}}
  assert add[1]=={'Move':{'kind':{'Local':base}}}
  rg=compact(find(fs[199]['body'],range_sid)['kind']['Assign'][1]['Aggregate']);assert rg[0]['Adt'][0]['id']=={'Adt':25}and rg[1]==[{'Move':{'kind':{'Local':starts}}},{'Move':{'kind':{'Local':ends}}}]
  for ref,a,b in zip(refs,slots,slots[1:]):
   dest,rhs=compact(find(fs[199]['body'],ref)['kind']['Assign']);assert dest['kind']=={'Local':b};r=rhs['Ref'];assert r['kind']=='Shared'and r['place']['kind']=={'Projection':[{'kind':{'Local':a}},'Deref']}and r['ptr_metadata']=={'Copy':{'kind':{'Projection':[{'kind':{'Local':a}},'PtrMetadata']}}}
  p=find(fs[199]['body'],pack)['kind']['Call']['call'];assert p['func']['Regular']['kind']['Fun']=={'Regular':319}and compact(p['args'])==[{'Move':{'kind':{'Local':slots[-1]}}}]
  bindings.append(dict(range_call=sid,pack_call=pack,range_constructor=range_sid,wrapped_end=add_sid,reborrows=refs,source_call=compact(c)))
 assert compact(find(fs[319]['body'],21973)['kind']['Assign'][1]['BinaryOp'])==['Le',{'Move':{'kind':{'Local':3}}},{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','4']}}}}}]
 assert find(fs[319]['body'],21975)['kind']['Assert']['assert']['expected']is True
 return dict(helper_instance=inst,environment=env,bindings=bindings,assertion_statement=21975)

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'RANGE-SLICE-TEMPLATE-D587.json').read_text());ps=parity();binding=certify(fs,g,t);controls={}
 for fid,sid,label in[(199,9597,'changed_width'),(199,9618,'changed_metadata_reborrow'),(319,21973,'changed_assertion')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_RangeSlice587227';s='''import PV_B3P_SliceMetadata581227
namespace PV_B3P_RangeSlice587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SliceMetadata581227
set_option autoImplicit false
/-- Actual helper318 metadata, two reborrows and source assertion319:21975. -/
def sourceState (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent start 4#usize 16 0 effects
theorem certificate {α : Type} (start : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState start effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (decide (observed.index ≤ observed.length) = true) ∧
      branch (decide (observed.index ≤ observed.length) = true) normal first =
        branch (decide (observed.index ≤ observed.length) = true) normal second :=
  event_certificate start 4#usize 16 0 effects observed ran normal first second
#print axioms certificate
end PV_B3P_RangeSlice587227
'''
 inst=next(k for k,v in g['instances'].items()if v['id']==319);x=dict(rows=[dict(instance=inst,function_id=319,statement=21975,lemma=name+'.certificate')],count=1,chunks=[name],binding=binding,source_parity=ps,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 array/slice range scalar metadata and caller reborrow projection plus named kernel assertion guard',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',compiler_boundary='V370: usize arithmetic/checked_sub, array unsizing and aggregate_raw_ptr metadata; no new trust field',failure_paths='invalid range has no downstream assertion observation; helper318 panic exclusion/whole-body binding is still OPEN',whole_caller_association=False,opaque_helper318_complete=False,premises_removed=[])
 for p,s in {D/'lean'/(name+'.lean'):s,R/'RANGE-SLICE-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_assertions=1,check=a.check,controls=controls)))
if __name__=='__main__':main()
