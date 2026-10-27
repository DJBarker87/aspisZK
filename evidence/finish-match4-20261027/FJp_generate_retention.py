"""Prefix-only proof refactoring: retain the existing root-copy output."""
from pathlib import Path
R=Path(__file__).resolve().parents[2]
L=R/'lean'
results=['ResultSelected','ActualResult','ClosedResult','DirectResult','LiteralResult','LiteralFull','R3Result','SafResult','FinalResult','R5Result','R6Result','Result']
proofs=['PairSelected','ActualPair','ClosedPair','DirectPair','LiteralPair','LiteralTop','R3Top','SafResult','SafTop','FinalResult','FinalTop','Deployed','Extract','Source','R5Close','R6Result','Release']
oldnames=['FIs_P2P_'+n for n in set(results+proofs)]+['FIs_Rc7_Native']
mapping={n:n.replace('FIs_P2P_','FJp_Ret_').replace('FIs_Rc7_Native','FJp_Ret_Rc7Native') for n in oldnames}
def transform(s):
 for a,b in sorted(mapping.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
 s=s.replace('fis_extract_source','fjp_retain_extract_source')
 return s
imports=set(['FJp_RootBinding'])
chunks=[]
for n in results:
 name='FIs_P2P_'+n
 src=(L/(name+'.lean')).read_text()
 imports.add(name)
 body=src[src.index('set_option autoImplicit false'):]
 if 'theorem ' in body:
  body=body[:body.index('theorem ')]+'end AspisR1.'+name+'\nend\n'
 body=transform(body)
 needle='    ∃ tx2 : Cons_Native.Witness,'
 assert needle in body,name
 body=body.replace(needle,'    FJp_RootBinding.Holds f.proof run.root ∧\n'+needle,1)
 chunks.append(body)
(L/'FJp_RetDefinitions.lean').write_text(''.join('import '+x+'\n' for x in sorted(imports))+'\n'+'\n'.join(chunks))
# Individual source proof bodies go into two dependency-ordered proof modules.
first=['PairSelected','ActualPair','ClosedPair','DirectPair','LiteralPair','LiteralTop','R3Top']
second=['SafResult','SafTop','FinalResult','FinalTop','Deployed','Extract','Source','R5Close','R6Result','Release']
for group,out,prior in [(first,'FJp_RetPrefix','FJp_RetDefinitions'),(second,'FJp_RetSuffix','FJp_RetPrefix')]:
 imports=set([prior]);chunks=[]
 for n in group:
  name='FIs_P2P_'+n
  src=(L/(name+'.lean')).read_text();imports.add(name)
  body=src[src.index('set_option autoImplicit false'):]
  if n in results:
   idx=body.index('def Outcome');end=body.index('theorem ',idx)
   body=body[:idx]+body[end:]
  body=transform(body)
  body=body.replace(',run,tx2,',',run,rootBinding,tx2,').replace(',run,tx2run,',',run,rootBinding,tx2run,')
  if n=='PairSelected':
   needle='saved f s pairCuts\n  have control'
   assert needle in body
   body=body.replace(needle,'saved f s pairCuts\n  have rootBinding : FJp_RootBinding.Holds f.proof run.root := ⟨rootView,rootRange,rootCopy⟩\n  have control')
  if n=='Extract': body='section\n'+body+'\nend\n'
  chunks.append(body)
 (L/(out+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(imports))+'\n'+'\n'.join(chunks))
# Last native factory theorem keeps the same output fact.
src=(L/'FIs_Rc7_Native.lean').read_text();body=src[src.index('set_option autoImplicit false'):];body=transform(body)
(L/'FJp_RetRc7.lean').write_text('import FJp_RetSuffix\nimport FIs_Rc7_Native\n'+body)
