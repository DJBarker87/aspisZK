#!/usr/bin/env python3
"""NPH_ (1): read-only call-site census over the L187 replay sources. For each of the 28
domain-lemma kernels, list every reached (deployed_splitB REACHABLE) definition whose body
names the kernel, with the body text. Usage: NPH_callers_host.py CONE.json REACH.txt SRC OUT"""
import json,sys,re,pathlib
cone=json.load(open(sys.argv[1]))['definitions'];reach=set(open(sys.argv[2]).read().split());src=pathlib.Path(sys.argv[3])
K=[x for x in cone if x['nph_judgment'].startswith('DOMAIN_LEMMA')]
mods=sorted(set(x['gate_file_in_L187_replay'] for x in K))
# all lean files that mention any kernel short name with its namespace prefix
out={}
files=[p for p in src.rglob('*.lean')]
for x in K:
  out[x['definition']]=[]
names={x['definition']:x['definition'] for x in K}
defre=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|partial\s+)*def\s+(\S+)',re.M)
for p in files:
  t=p.read_text()
  if 'Funs' not in p.name and 'Source' not in p.name and 'Native' not in p.name and 'Slice' not in p.name and 'Extract' not in p.name and 'Model' not in p.name: pass
  ns=None
  m=re.search(r'^namespace\s+(\S+)',t,re.M); ns=m.group(1) if m else ''
  starts=[(m.start(),m.group(1)) for m in defre.finditer(t)]
  for i,(s,n) in enumerate(starts):
    e=starts[i+1][0] if i+1<len(starts) else len(t)
    body=t[s:e]; full=(ns+'.'+n) if ns and not n.startswith(ns+'.') else n
    if full not in reach: continue
    for kd in names:
      short=kd[len(ns)+1:] if ns and kd.startswith(ns+'.') else None
      if (short and re.search(r'(?<![\w.])'+re.escape(short)+r'\b',body) and full!=kd) or (kd in body and full!=kd):
        out[kd].append(dict(caller=full,file=str(p.relative_to(src)),body=body[:2500]))
json.dump(out,open(sys.argv[4],'w'),indent=1)
for k,v in out.items(): print(len(v),k,sorted(set(c['caller'].split('.')[-1] if False else c['caller'] for c in v))[:12])
