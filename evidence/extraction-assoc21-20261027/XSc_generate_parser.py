from pathlib import Path
import re,json,hashlib,sys
def emit(path,content):
 if "--check" in sys.argv:
  assert path.read_text()==content,str(path)+" generated-source drift"
 else:path.write_text(content)
E=Path(__file__).resolve().parent
P=Path('evidence/extraction-assoc6-20261027/XRn_Join_Funs.lean')
s=P.read_text();s=s[s.index('def r1_wire.Prefix.parse\n'):];s=s[:s.index('\n/--')]
lines=s.splitlines();starts=[]
for i,l in enumerate(lines):
 if re.search(r'let \w+ ←',l):
  chunk=' '.join(x.strip() for x in lines[i:i+5])
  m=re.match(r'let \w+ ← r1_wire.parse_record_at bytes (\d+)#u8',chunk)
  if m:starts.append((int(m[1]),i,len(l)-len(l.lstrip())))
assert len(starts)==27,starts
term=next(i for i,l in enumerate(lines) if 'let i1 :=' in l)
starts.append((27,term,len(lines[term])-len(lines[term].lstrip())))
prev=lambda n:['r0']+[f'r{j}1' for j in range(1,n)] if n else []
def sig(n):
 return '(bytes : Slice U8) (root : Array U8 32#usize) '+ ('('+' '.join(prev(n))+' : Slice U8) ' if n else '')+'(offset : Usize)'
def args(n):return 'bytes root '+(' '.join(prev(n))+' ' if n else '')+'offset'
def chunk(n):
 _,i,indent=starts[n];end=i+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=indent):end+=1
 ls=lines[i:end]
 # Substitute only the pre-existing current offset; all internal suffix names remain literal.
 text='\n'.join(l[indent:] for l in ls)
 old='32#usize' if n==0 else ('offset' if n==1 else f'offset{n-1}')
 if n==0:text=text.replace('0#u8 32#usize','0#u8 offset',1)
 else:text=re.sub(r'\b'+old+r'\b','offset',text)
 return text
# Each definition is one source continuation cut. The final reconstruction is
# kernel reflexivity against the actual entire parser, not a source-shape claim.
defs=[]
for n in reversed(range(28)):
 c=chunk(n)
 if n<27:
  sub=chunk(n+1)
  # Locate the original suffix by its lexical line range before substitutions.
  _,start,ind=starts[n+1];_,base,bind=starts[n]
  end=start+1
  while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=ind):end+=1
  original='\n'.join(l[bind:] for l in lines[start:end])
  current='32#usize' if n==0 else ('offset' if n==1 else f'offset{n-1}')
  if n>0:original=re.sub(r'\b'+current+r'\b','offset',original)
  # Passed next offset is defined by THIS stage's match-pattern.
  newoff='offset' if n==0 else f'offset{n}'
  call=' '*(ind-bind)+f'tail{n+1} bytes root '+(' '.join(prev(n+1))+' ')+newoff
  assert original in c,(n,original[:100],c[:150])
  c=c.replace(original,call,1)
 defs.append(f'def tail{n} {sig(n)} : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do\n'+'\n'.join(' '+l for l in c.splitlines())+'\n')
emit(E/'XSc_ParseCuts.lean','import XRz_ParseFold\nopen Aeneas Aeneas.Std Result XRn_Join_Release\nset_option autoImplicit false\nnamespace XSc_ParseCuts\n'+ '\n'.join(defs)+'end XSc_ParseCuts\n')
for n in reversed(range(28)):
 name=f'XSc_ParseStage{n:02}'
 imp='XSc_ParseCuts' if n==27 else f'XSc_ParseStage{n+1:02}'
 code=f'import {imp}\nimport XSc_ParseResume\nopen Aeneas Aeneas.Std Result XRn_Join_Release\nset_option autoImplicit false\nnamespace {name}\ntheorem source {sig(n)} :\n XSc_ParseCuts.tail{n} {args(n)} =\n XSc_ParseResume.run bytes root {n} {27-n} ([{",".join(prev(n))}],offset) := by\n'
 if n==27:
  code+=' unfold XSc_ParseCuts.tail27 XSc_ParseResume.run XRx_TryDriver.run XRz_ParseFold.finish\n rfl\n'
 else:
  code+=f''' unfold XSc_ParseCuts.tail{n}
 rw [XSc_ParseResume.advance]
 simp only [XRz_ParseFold.row,Nat.reduceLT,_root_.dite_true,U8.ofNat,Nat.reduceAdd]
 congr 1
 funext parsed
 cases parsed with
 | Err e => rfl
 | Ok pair =>
  rcases pair with ⟨record,next⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  dsimp! only
  simpa only [List.append_nil,List.cons_append,List.nil_append] using
   XSc_ParseStage{n+1:02}.source bytes root '''+(' '.join(prev(n))+' ' if n else '')+'''record next
'''
 code+='#print axioms source\nend '+name+'\n';emit(E/(name+'.lean'),code)
emit(E/'XSc_parser_generation.json',json.dumps({'source':str(P),'sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'cuts':28,'method':'literal continuation cuts; one generic symbolic resume advance; reconstruct whole actual parser by kernel reflexivity'},indent=2))
