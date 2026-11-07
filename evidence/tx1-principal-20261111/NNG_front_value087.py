from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NNG_Front087.lean').read_text().replace('namespace AspisR1.NNG_Front087','namespace AspisR1.NNG_FrontValue087').replace('end AspisR1.NNG_Front087','end AspisR1.NNG_FrontValue087').replace('NNG_Front087.semantic','NNG_FrontValue087.semantic').replace('Code (FrontOut H)','Result (FrontOut H)').replace('pure (','ok (')
def endparen(text,start):
 assert text[start]=='('
 depth=0
 for i in range(start,len(text)):
  if text[i]=='(':depth+=1
  elif text[i]==')':
   depth-=1
   if depth==0:return i+1
 raise ValueError('unbalanced')
while True:
 m=re.search(r'invoke "[^"]+"\s*',s)
 if not m:break
 a=m.end();b=endparen(s,a);c=b
 while s[c].isspace():c+=1
 d=endparen(s,c)
 s=s[:m.start()]+s[c:d]+s[d:]
s=s.replace('NMP_PrepareSteps NMT_CallTree','NMP_PrepareSteps')
(E/'NNG_FrontValue087.lean').write_text(s)
