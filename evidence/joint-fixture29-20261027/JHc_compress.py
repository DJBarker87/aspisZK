"""Expose only SHA block inputs/results and checked equations.

Preserves JGy's symbolic step certificate and its exported block equations;
round schedules/registers are proof terms instead of imported declarations.
No dot, gate, line, or query-loop arithmetic is regenerated.
"""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
old=R/'evidence/joint-fixture27-20261027'
groups=json.loads((old/'JGy_GROUPS.json').read_text())
consumers=json.loads((old/'JGy_CONSUMERS.json').read_text())
modules=[g['module'] for g in groups]+[c['module'] for c in consumers]+['JGy_RootReads','JGy_Batch','JGy_PreBatch','JGy_BatchFrontier','JGy_TX1']
modmap={m:m.replace('JGy_','JHc_',1) for m in modules}
nsmap={'JGy_Gr_':'JHc_Gr_','JGy_Gu_':'JHc_Gu_','JGy_Gw_':'JHc_Gw_'}
def rename(s):
 for a,b in nsmap.items():s=s.replace(a,b)
 return re.sub(r'\bJGy_\w+\b',lambda m:modmap.get(m[0],m[0]),s)
def block(m):
 b=m[2]
 defs=dict(re.findall(r'^def ((?:w|s)\d\d) : [^\n:=]+ := ([^\n]+)',b,re.M))
 assert len(defs)==130
 b=re.sub(r'^def (?:w|s)\d\d : [^\n]+\n','',b,flags=re.M)
 b=re.sub(r'^theorem parsed : [^\n]+\n#print axioms parsed\n','',b,flags=re.M)
 b=b.replace('theorem checked : compress start (words input)=result := by\n','theorem checked : compress start (words input)=result := by\n  have parsed : words input=w00 := by rfl\n')
 b=re.sub(r'\b(?:w|s)\d\d\b',lambda x:'('+defs[x[0]]+')',b)
 return m[1]+b+m[3]
manifest=[]
for m in modules:
 source=(R/'lean'/f'{m}.lean').read_text();s=source
 if m in [g['module'] for g in groups]:
  s=re.sub(r'(namespace B\d\d\n)(.*?)(end B\d\d)',block,s,flags=re.S)
 s=rename(s);out=R/'lean'/f'{modmap[m]}.lean'
 if '--check' in sys.argv:assert out.read_text()==s,m
 else:out.write_text(s)
 manifest.append(dict(module=modmap[m],original=m,original_sha256=hashlib.sha256(source.encode()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),imports=re.findall(r'^import (\w+)',s,re.M)))
(P/'JHc_COMPRESSION.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Validated' if '--check' in sys.argv else 'Generated',len(manifest),'modules')
