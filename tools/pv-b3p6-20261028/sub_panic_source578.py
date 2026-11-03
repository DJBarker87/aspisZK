"""Compose every captured input edge of helper317 with its exact panic test."""
from pathlib import Path
import argparse,copy,hashlib,json,lzma,re,subprocess
from initializer_source578 import compact,find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def tokens(s):
 lex=re.findall(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',s,re.S)
 return[x for x in lex if not x.startswith('//')and not x.startswith('/*')]
def item(s,needle):
 s=s[s.index(needle):];t=tokens(s);start=t.index('{');depth=1;end=start+1
 while depth:depth+=(t[end]=='{')-(t[end]=='}');end+=1
 return t[:end]
def certify(f,template):
 assert compact(f['body'])==template
 for sid,slot in [(21903,1),(21905,2)]:
  op,arg=find(f['body'],sid)['kind']['Assign'][1]['UnaryOp'];assert op=={'Cast':{'Scalar':[{'UInt':'Usize'},{'UInt':'U64'}]}}and arg['Copy']['kind']=={'Local':slot}
 binary=find(f['body'],21906)['kind']['Assign'][1]['BinaryOp'];assert binary[0]=='SubChecked'and binary[1]['Move']['kind']=={'Local':8}and binary[2]['Move']['kind']=={'Local':9}
 assert find(f['body'],21909)['kind']['Assign'][1]['Use'][0]['Copy']['kind']['Projection'][1]=={'Field':[{'Tuple':2},1]}
 cond,yes,no=find(f['body'],21919)['kind']['Switch']['If'];assert cond['Copy']['kind']=={'Local':6}and yes['statements']==[]and no['statements'][-1]['kind']=='Return'
 call=find(f['body'],21954)['kind']['Call']['call'];assert call['func']['Regular']['kind']['Fun']=={'Regular':412}
 return dict(casts=[21903,21905],checked_subtraction=21906,overflow_projection=21909,source_branch=21919,panic_call=21954)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--capture',action='store_true');a=p.parse_args()
 if a.capture:
  code="""from pathlib import Path
import json
out=[]
for v in ['1.94.1','nightly-2026-06-01']:
 for name in ['num/uint_macros.rs','ub_checks.rs']:
  p=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'/name
  out.append(dict(version=v,name=name,path=str(p),source=p.read_text()))
print(json.dumps(out))
"""
  for row in json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)):
   data=row.pop('source').encode();target=R/'std578-source'/row['version']/(row['name']+'.xz');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(lzma.compress(data,preset=6))
 comparisons=[]
 for name,needle in [('num/uint_macros.rs','unsafe fn unchecked_sub('),('num/uint_macros.rs','fn overflowing_sub('),('ub_checks.rs','macro_rules! assert_unsafe_precondition')]:
  bodies={};pins={}
  for v in ['1.94.1','nightly-2026-06-01']:
   path=R/'std578-source'/v/(name+'.xz');data=lzma.decompress(path.read_bytes());bodies[v]=item(data.decode(),needle);pins[v]=dict(path=str(path),sha256=sha(data))
  assert bodies['1.94.1']==bodies['nightly-2026-06-01'],(name,needle)
  comparisons.append(dict(name=name,needle=needle,source_pins=pins,tokens=bodies['1.94.1'],tokens_identical=True))
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];f=next(f for f in ll['fun_decls']if f and f['def_id']==317);template=json.loads((R/'SUB-PANIC-TEMPLATE-D578.json').read_text());source=certify(f,template)
 graph=json.loads((I/'direct3-instantiated-callcone.json').read_text());incoming=[e for e in graph['edges']if e['callee_id']==317];assert{int(e['caller'].split(':')[0])for e in incoming}=={192,237}and len(incoming)==2
 callers=json.loads((R/'SLICE-SOURCE-D578.json').read_text())['rows'];assert{e['caller']for e in incoming}=={r['instance']for r in callers}
 controls={}
 for label,edit in {
  'narrowing_cast':lambda b:find(b,21903)['kind']['Assign'][1]['UnaryOp'][0]['Cast']['Scalar'].__setitem__(1,{'UInt':'U8'}),
  'different_checked_operation':lambda b:find(b,21906)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,'AddChecked'),
  'different_overflow_flag':lambda b:find(b,21909)['kind']['Assign'][1]['Use'][0]['Copy']['kind']['Projection'][1]['Field'].__setitem__(1,0),
  'nonoverflow_fallthrough':lambda b:find(b,21919)['kind']['Switch']['If'][2]['statements'][-1].__setitem__('kind','Nop'),
 }.items():
  changed=copy.deepcopy(f);edit(changed)
  try:certify(changed,template)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 row=dict(instance=next(k for k,v in graph['instances'].items()if v['id']==317),statement=21954,lemma='PV_B3P_SubPanicFamily578227.family_certificate',incoming_edges=incoming,source_argument_certificates=callers,source=source)
 meta=dict(rows=[row],count=1,llbc_sha256=sha(raw),template_sha256=sha((R/'SUB-PANIC-TEMPLATE-D578.json').read_bytes()),source_parity=comparisons,negative_controls=controls,evidence_class='script-checked own-1 helper317 source test and ALL captured incoming guards, composed with Lean overflow/panic exclusion',native_pointer_validity=False,opaque_panic_interior_assumed=False,whole_caller_association=False,premises_removed=[])
 family='''import PV_B3P_SubPanicEvents578227
namespace PV_B3P_SubPanicFamily578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SubPanicEvents578227
set_option autoImplicit false
/-- All two captured incoming source-event families; no guard input. -/
def sourceState (_caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize) : Bool :=
  !panicEvent zeroSized checks encodedEnd

theorem family_guard (caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize) :
    sourceState caller zeroSized checks encodedEnd = true := panic_guard zeroSized checks encodedEnd

theorem family_certificate {α : Type} (caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize)
    (normal first second : Result α) :
    ¬ diagnostic (sourceState caller zeroSized checks encodedEnd = true) ∧
      branch (sourceState caller zeroSized checks encodedEnd = true) normal first =
        branch (sourceState caller zeroSized checks encodedEnd = true) normal second :=
  panic_certificate zeroSized checks encodedEnd normal first second
#print axioms family_guard
#print axioms family_certificate
end PV_B3P_SubPanicFamily578227
'''
 for out,s in {R/'SUB-PANIC-SOURCE-D578.json':json.dumps(meta,indent=2)+'\n',D/'lean/PV_B3P_SubPanicFamily578227.lean':family}.items():
  if a.check:assert out.read_text()==s
  else:out.write_text(s)
 print(json.dumps(dict(local_panic_certificate=1,incoming_source_edges=len(incoming),source_parity_items=len(comparisons),check=a.check)))
if __name__=='__main__':main()
