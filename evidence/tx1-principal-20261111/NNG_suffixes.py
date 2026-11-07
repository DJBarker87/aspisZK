"""Fission the fresh symbolic body into source-ordered occurrence continuations.
Raw body is unchanged; only lexical continuations become named functions.
No callee is evaluated, unfolded or replaced by a successful value.
"""
from pathlib import Path
import json,re,textwrap
E=Path(__file__).resolve().parent
f=(E/'NNG_generated/NNG_verify_finish/Funs.lean').read_text()
b=f[f.index('def r1_semantic.verify_finish '):]
b=b[b.index('  := do')+len('  := do'):b.index('\nend NNG_verify_finish')]
b=re.sub(r'\bNNG_call_(\d+)\b',r'c.c\1',b)
lines=b.strip('\n').splitlines()
points=[]
for i,l in enumerate(lines):
 st=l.strip();name=None
 if st.startswith('let ') and ('←' in st or st.endswith('←')):
  lhs=st[4:st.index('←')].strip()
  if lhs.startswith('('):
   name=lhs[1:lhs.index(',')].strip()
  else:name=lhs
  if name.startswith('cf'):continue
 elif st.startswith('c.c9 '):name='mark'+re.search(r'(\d+)#u8',st)[1]
 elif st=='if b':name='terminalGuard'
 elif st=='if b1':name='circleGuard'
 if name is None:continue
 indent=len(l)-len(l.lstrip());end=i+1
 while end<len(lines):
  if lines[end].strip() and len(lines[end])-len(lines[end].lstrip())<indent:break
  end+=1
 points.append(dict(start=i,end=end,indent=indent,name=name))
# All non-input values live in one lexical parent. Types come directly from
# the fresh body; these are data arguments, never success hypotheses.
Q='Q';T='r1_wire.SemanticTranscript H';Rec='r1_wire.ValidatedRecord';Pt='aspis_core.circle.SecureCirclePoint';BR='Array U8 32#usize'
types={k:Q for k in ['running','val2','q','mask','q1','q2','q3','masked_terminal']}
types.update(alpha='Alpha',transcript1=T,val1='Claims',a='Array Q 16#usize',a1='Alpha',a2='K29',vr=Rec,val3='K29',b='Bool',state_before_z0=BR,vr1=Rec,transcript2=T,val4=Pt,vr2=Rec,val5='K29',vr3=Rec,transcript3=T,val6=Pt,b1='Bool',val7='Slice U8',a3=BR)
types['r2']='core.result.Result Q aspis_core.state_only_prefix.r0.Error'
types['r11']='core.result.Result (Array U8 32#usize) core.array.TryFromSliceError'
types.update(r4='core.result.Result r1_wire.ValidatedRecord r1_wire.Error',r7='core.result.Result r1_wire.ValidatedRecord r1_wire.Error')
lookup={p['start']:p for p in points}
for p in points:
 src='\n'.join(lines[p['start']:p['end']])
 defined=set()
 for m in re.finditer(r'\blet\s+(.+?)\s*(?:←|:=)',src):defined.update(re.findall(r'\b\w+\b',m[1]))
 for m in re.finditer(r'ControlFlow\.(?:Continue|Break)\s+(\w+)',src):defined.add(m[1])
 p['free']=[n for n in types if n not in defined and re.search(r'(?<![\w.])'+n+r'(?![\w.])',src)]
 p['args']=''.join(' ('+n+' : '+types[n]+')' for n in p['free'])
 p['app']=' '.join(p['free'])
def call(p):return 'f_'+p['name']+' c s'+(' '+p['app'] if p['app'] else '')
def render(p):
 out=[];i=p['start']
 while i<p['end']:
  if i!=p['start'] and i in lookup:
   q=lookup[i];assert q['end']<=p['end']
   out.append(' '*q['indent']+call(q));i=q['end']
  else:out.append(lines[i]);i+=1
 return textwrap.indent(textwrap.dedent('\n'.join(out)),'  ')
header='''import NNG_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
'''
aliases='  let aspis_coredigestDigest32Inst := s.digest\n  let public1 := s.publicValue\n  let prefix1 := s.prefixValue\n  let transcript := s.transcript\n  let challenges := s.challenges\n  let obs := s.observer\n'
text=header
for p in reversed(points):
 text+='\ndef f_'+p['name']+' {H W : Type} (c : Calls) (s : Parent H W)'+p['args']+' : Result (Output H) := do\n'+aliases+render(p)+'\n'
text+='\nend AspisR1.NNG_SourceSuffixes\n'
(E/'NNG_SourceSuffixes.lean').write_text(text)
for ix,p in enumerate(points):
 mod='NNG_Step_'+p['name']
 st=header.replace('import NNG_EmittedContext','import NNG_SourceSuffixes')
 st+='\n/-- Fresh source occurrence '+str(ix)+': SAME typed values and complete Result continuation. Support until concrete child installation. -/\n'
 st+='theorem occurrence_'+p['name']+' {H W : Type} (c : Calls) (s : Parent H W)'+p['args']+' :\n '+call(p)+' = (do\n'+textwrap.indent(aliases+render(p),'  ')+') := rfl\n'
 st+='#print axioms occurrence_'+p['name']+'\nend AspisR1.NNG_SourceSuffixes\n'
 (E/(mod+'.lean')).write_text(st)
(E/'NNG_SOURCE_OCCURRENCES.json').write_text(json.dumps(points,indent=1)+'\n')
(E/'NNG_SourceEmitted.lean').write_text(header.replace('import NNG_EmittedContext','import NNG_SourceSuffixes')+'''
/-- Lexical fission of the ACTUAL fresh body; all opaque callees are still
explicit and complete. No native observation or successful child is assumed. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 f_r c s=NNG_Emitted.emitted c s := by rfl
#print axioms emitted
end AspisR1.NNG_SourceSuffixes
''')
print('Fissioned',len(points),'symbolic source occurrences')
