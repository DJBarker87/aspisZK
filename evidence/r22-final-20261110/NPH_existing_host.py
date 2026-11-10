#!/usr/bin/env python3
"""NPH_ T1 helper (read-only over the L187 replayed closure sources): for each checked/mixed
cone definition, list closure theorems whose statement mentions the definition followed by
`= ok`/`= .ok`/`⦃` (a success or totality conclusion), with their full signature.
Screen labels: TOTAL_SCREEN (no Prop hypothesis), DOMAIN_SCREEN (Prop hypotheses, none
an `= ok` premise), ACCEPTED_SCREEN (a success premise). Labels are a search aid only."""
import json,sys,re,pathlib
R=json.load(open(sys.argv[1]));src=pathlib.Path(sys.argv[2])
files=list(src.rglob('*.lean'))
texts={}
for f in files:
  try: texts[f]=f.read_text()
  except Exception: pass
thm=re.compile(r'^(?:private\s+)?(?:theorem|lemma)\s+(\S+)(.*?)(?::=|\bwhere\b)',re.S|re.M)
out={}
targets={}
for r in R:
  if r['cls']=='wrapping_configuration': continue
  d=r['definition']; parts=d.split('.')
  keys={d}
  if len(parts)>2: keys.add('.'.join(parts[1:]))
  targets[d]=keys
for f,t in texts.items():
  if 'Funs.lean' in f.name and f.parent.name!='src': pass
  hits=[k for d,ks in targets.items() for k in ks if k in t]
  if not hits: continue
  for m in thm.finditer(t):
    sig=m.group(0)
    if len(sig)>3000: continue
    for d,ks in targets.items():
      for k in ks:
        i=sig.find(k)
        if i<0: continue
        after=sig[i:i+400]
        if re.search(r'=\s*\.?ok\b|⦃|∃',after):
          hyp=sig[:sig.find(k)]
          prem=re.findall(r'\(h\w*\s*:[^)]*\)',sig)
          lab='ACCEPTED_SCREEN' if any(re.search(r'=\s*\.?ok',p) for p in prem) else ('DOMAIN_SCREEN' if prem else 'TOTAL_SCREEN')
          out.setdefault(d,[]).append(dict(file=str(f.relative_to(src)),theorem=m.group(1),screen=lab,signature=re.sub(r'\s+',' ',sig)[:900]))
          break
      else: continue
json.dump(out,open(sys.argv[3],'w'),indent=1)
print(len(out),sum(len(v) for v in out.values()))
