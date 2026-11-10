#!/usr/bin/env python3
"""undrop.py <in.lean> <out.lean> <def name>...  restore PRV-FRESH-DROPPED blocks by def name (all later dropped blocks stay commented)."""
import re,sys
src,out,*names=sys.argv[1:]
s=open(src).read()
def rep(m):
    t=m.group(1)
    d=re.search(r'(?:^|\n)def\s+(\S+)',t)
    if d and d.group(1) in names: return t+'\n\n'
    return m.group(0)
s=re.sub(r'/- PRV-FRESH-DROPPED[^\n]*\n(.*?)\n-/\n\n?',rep,s,flags=re.S)
open(out,'w').write(s)
