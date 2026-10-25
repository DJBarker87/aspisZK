from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/100bit-spend-path-20261013/lean'; E=R/'evidence/port12count-20261024'
owned=[];audit=['import Port12COUNT_FirstReads','set_option pp.proofs false']
for p in sorted(L.glob('Port12COUNT_*.lean')):
 if p.stem=='Port12COUNT_Audit':continue
 for kind,name in re.findall(r'^\s*(?:@\[[^\n]+\]\s*)?(theorem|def)\s+(\w+)',p.read_text(),re.M):
  full='AspisR1.'+p.stem+'.'+name
  owned.append({'module':p.stem,'kind':kind,'name':full})
  audit.append('#print '+full)
  if kind=='theorem':audit.append('#print axioms '+full)
outputs={L/'Port12COUNT_Audit.lean':'\n'.join(audit)+'\n',E/'owned-declarations.json':json.dumps(owned,indent=2)+'\n'}
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print(json.dumps({'declarations':len(owned),'theorems':sum(d['kind']=='theorem' for d in owned),'check':'--check' in sys.argv}))
