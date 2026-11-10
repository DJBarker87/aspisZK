#!/usr/bin/env python3
"""PCUI_bundle.py OUT file1 file2 ...: exact concatenation of generated PRVEq files: all `import` lines hoisted (Aeneas first, then the gate imports in order),
bodies concatenated unchanged otherwise. Writes OUT.lean and OUT.bundle.json (file -> line offset)."""
import sys,re,json
out=sys.argv[1];files=sys.argv[2:]
imps=[];bodies=[];offs={};n=0
head=[]
for f in files:
    lines=open(f).read().split('\n')
    keep=[]
    for l in lines:
        if l.startswith('import '):
            if l not in imps: imps.append(l)
        else: keep.append(l)
    bodies.append((f,keep))
imps.sort(key=lambda l:(l!='import Aeneas',))
text='\n'.join(imps)+'\n'
n=len(text.split('\n'))-1
for f,keep in bodies:
    offs[f]=n; text+='\n'.join(keep)+'\n'; n+=len(keep)
open(out+'.lean','w').write(text);json.dump(offs,open(out+'.bundle.json','w'),indent=1)
print(out,len(files),'files',n,'lines')
