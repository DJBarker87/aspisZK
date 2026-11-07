#!/usr/bin/env python3
"""Conservative lexical declaration names with actual namespace scope.
No elaboration claim: retain NKT ambiguity separately, never cross-product scopes.
"""
import re
def uncomment(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out+=[' ',' '];i+=2
   elif s.startswith('-/',i):depth-=1;out+=[' ',' '];i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\' and i+1<len(s):out+=[' ',' '];i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out+=[' ',' '];i+=2
  elif s.startswith('--',i):
   end=s.find('\n',i);end=len(s) if end<0 else end;out.extend(' '*(end-i));i=end
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 assert depth==0,'unterminated comment'
 return ''.join(out)
def declarations(s):
 clean=uncomment(s);scope=[];out=[]
 rx=re.compile(r'(?m)^\s*(?:(namespace)\s+(\S+)|(end)\b(?:[ \t]+(\S+))?|((?:noncomputable[ \t]+)?section)\b|(?:(?:noncomputable|private|protected)[ \t]+)?(def|abbrev|structure|inductive|theorem|lemma)\s+([^\s({:]+))')
 for m in rx.finditer(clean):
  if m[1]:scope.append(('namespace',m[2]))
  elif m[3]:
   if scope:scope.pop()
  elif m[5]:scope.append(('section',''))
  else:
   ns='.'.join(x[1] for x in scope if x[0]=='namespace');name=m[7]
   out.append(dict(name=(ns+'.' if ns else '')+name,short_name=name,kind=m[6],private=bool(re.search(r'\bprivate\s+',clean[m.start():m.end()])),line=clean.count('\n',0,m.start())+1))
 return out
