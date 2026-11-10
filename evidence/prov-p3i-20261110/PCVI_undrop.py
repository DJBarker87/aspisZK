#!/usr/bin/env python3
"""PCVI_undrop: restore PRV-FRESH-DROPPED blocks of a generated PRVEq file and turn PRV-OBLIGATION comments into `rfl` theorem attempts.
usage: PCVI_undrop.py in.lean out.lean 'note'"""
import sys,re,pathlib
src,dst,note=sys.argv[1:4];defsonly=len(sys.argv)>4 and sys.argv[4]=='defsonly'
t=pathlib.Path(src).read_text().split('\n')
out=[];i=0;blocks=0
while i<len(t):
    l=t[i]
    if l.startswith('/- PRV-FRESH-DROPPED'):
        j=i+1
        while t[j]!='-/': j+=1
        out+=t[i+1:j];i=j+1;blocks+=1;continue
    out.append(l);i+=1
s='\n'.join(out)
def repl(m):
    if defsonly: return '-- obligation (not attempted in this shape): %s'%m.group(1)
    return 'theorem %s : %s := by\n  rfl\n#print axioms %s'%(m.group(1),m.group(2),m.group(1))
s2,n=re.subn(r'/- PRV-OBLIGATION \(transport-needed; P3\): (\S+) : (.*?)\n   last probe error: [^\n]*-/',repl,s,flags=re.S)
pathlib.Path(dst).write_text('-- PCVI_ '+note+' (undropped %d blocks, %d obligations as rfl attempts)\n'%(blocks,n)+s2)
print(blocks,n)
