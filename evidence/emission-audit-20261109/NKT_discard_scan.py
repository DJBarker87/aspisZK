#!/usr/bin/env python3
"""Flag discarded Try residual conversions in imported or raw emitted definitions."""
import json,pathlib,re
from NKT_checker import Git,sha
P=pathlib.Path(__file__).parent

def main():
 a=json.load(open(P/'NKT_AUDIT.json'));g=Git(a['audit_revision']);out=[]
 paths={x['emission_path'] for x in a['functions']}
 for p in sorted(paths):
  text=g.text(p)
  for m in re.finditer(r'let _\s*←(?:(?!\n(?:def |/--)).){0,600}?\.from_residual',text,re.S):
   names=list(re.finditer(r'(?m)^def\s+(\S+)',text[:m.start()]))
   out.append({'path':p,'sha256':sha(g.read(p)),'definition':names[-1].group(1) if names else None,'line':text.count('\n',0,m.start())+1,'excerpt':text[m.start():m.end()+160]})
 P.joinpath('NKT_DISCARDS.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'discarded_residual_sites':len(out),'definitions':sorted({x['definition'] for x in out})}))
if __name__=='__main__':main()
