"""Fission the receipted NMT fresh tx1 body; no callee evaluation/substitution."""
from pathlib import Path
import re,textwrap,json,hashlib
E=Path(__file__).resolve().parent
src=(E/'NNG_NMT_inputs/NMT_tx1/Funs.lean').read_text()
b=src[src.index('def verifier.candidate.tx1 '):];b=b[b.index('  := do')+len('  := do'):b.index('\nend NMT_tx1')]
b=re.sub(r'\bNMT_call_(\d+)\b',r'c.c\1',b);lines=b.strip('\n').splitlines();points=[]
for i,l in enumerate(lines):
 st=l.strip();name=None
 if st.startswith('let ') and '←' in st:
  name=st[4:st.index('←')].strip();name=name[1:name.index(',')].strip() if name.startswith('(') else name
  if name.startswith('cf'):continue
 elif st.startswith('c.c11 '):name='mark'+re.search(r'Phase\.([A-Za-z]+)',st)[1]
 elif st.startswith('if k !='):name='guard'
 if name is None:continue
 indent=len(l)-len(l.lstrip());end=i+1
 while end<len(lines):
  if lines[end].strip() and len(lines[end])-len(lines[end].lstrip())<indent:break
  end+=1
 points.append(dict(start=i,end=end,indent=indent,name=name))
types={'we':'aspis_core.field.wide_exact.WideExact','g':'Array aspis_core.field.wide_exact.WideExact 29#usize','g1':'Array aspis_core.field.wide_exact.WideExact 29#usize','val':'verifier.Prepared','val1':'verifier.Accumulator','i':'Usize','i1':'Usize','s':'Slice U8','r4':'core.result.Result (Array U8 32#usize) core.array.TryFromSliceError','folded_root':'Array U8 32#usize','val2':'verifier.QueryGeometry','s1':'Slice aspis_core.field.QM31','val3':'verifier.BatchedWeights','val4':'verifier.Accumulator × verifier.BatchedWeights','a':'verifier.Accumulator','pending':'verifier.BatchedWeights','s2':'Slice aspis_core.field.QM31','deref_mut_back':'Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31','s3':'Slice aspis_core.field.QM31','v':'alloc.vec.Vec aspis_core.field.QM31','bytes':'alloc.vec.Vec U8'}
lookup={p['start']:p for p in points}
for p in points:
 text='\n'.join(lines[p['start']:p['end']]);defined=set()
 for m in re.finditer(r'\blet\s+(.+?)\s*(?:←|:=)',text):defined.update(re.findall(r'\b\w+\b',m[1]))
 for m in re.finditer(r'ControlFlow\.(?:Continue|Break)\s+(\w+)',text):defined.add(m[1])
 p['free']=[n for n in types if n not in defined and re.search(r'(?<![\w.])'+n+r'(?![\w.])',text)]
 p['args']=''.join(' ('+n+' : '+types[n]+')'for n in p['free']);p['app']=' '.join(p['free'])
def call(p):return 'f_'+p['name']+' c parent'+(' '+p['app'] if p['app'] else '')
def render(p):
 out=[];i=p['start']
 while i<p['end']:
  if i!=p['start'] and i in lookup:
   q=lookup[i];assert q['end']<=p['end'];out.append(' '*q['indent']+call(q));i=q['end']
  else:out.append(lines[i]);i+=1
 return textwrap.indent(textwrap.dedent('\n'.join(out)),'  ')
alias='''  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
'''
text='''import NNG_Context094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Suffix094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094
'''
for p in reversed(points):text+='\ndef f_'+p['name']+' {H : Type} (c : Calls) (parent : Parent H)'+p['args']+' : Result Output := do\n'+alias+render(p)+'\n'
text+='''
theorem source {H : Type} (c : Calls) (parent : Parent H) :
 f_guard c parent=NNG_Context094.body c parent := by rfl
#print axioms source
end AspisR1.NNG_Suffix094
'''
(E/'NNG_Suffix094.lean').write_text(text)
(E/'NNG_FISSION094.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(src.encode()).hexdigest(),output_sha256=hashlib.sha256(text.encode()).hexdigest(),occurrences=points,no_callee_substitution=True,no_credit_claim=True),indent=1))
print('Fissioned',len(points),'source occurrences')
