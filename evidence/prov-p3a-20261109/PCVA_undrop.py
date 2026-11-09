#!/usr/bin/env python3
"""PCVA_undrop.py IN OUT: turn every `/- PRV-FRESH-DROPPED ...` block comment (as emitted by the P5 generator) back into live
Lean text, so that the dropped fresh declarations are elaborated and their real errors become visible. Diagnostic tool only."""
import sys,re
src=open(sys.argv[1]).read().split('\n');out=[];i=0
while i<len(src):
    l=src[i]
    if l.startswith('/- PRV-FRESH-DROPPED'):
        out.append('-- undropped: '+l[:60]); i+=1
        while src[i]!='-/': out.append(src[i]); i+=1
        i+=1; continue
    out.append(l); i+=1
open(sys.argv[2],'w').write('\n'.join(out))
