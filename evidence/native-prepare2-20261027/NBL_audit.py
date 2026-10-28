"""Generate one final coimport + printed-axioms audit from accepted source roots."""
from pathlib import Path
import re,json,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
files=sorted((R/'lean').glob('NBL_*.lean'))
roots=[]
out=['import NBA_Audit']
for p in files:
 if p.stem=='NBL_Audit':continue
 s=p.read_text();out.append('import '+p.stem)
 ns=re.search(r'^namespace ([\w.]+)',s,re.M).group(1)
 for name in re.findall(r'^#print axioms ([\w.]+)',s,re.M):
  root=name if '.' in name else ns+'.'+name
  if root not in roots:roots.append(root)
out+=['set_option autoImplicit false','set_option pp.fullNames true']
out+=['#print axioms '+n for n in roots]
out+=['#check @AspisR1.NBL_ViewNatural.source','#check @AspisR1.NBL_ViewDomains.source',
       '#check @AspisR1.NBL_PrepareHashTrace.source',
       '#check @AspisR1.NBL_PrepareHashReject.source']
target=R/'lean/NBL_Audit.lean';s='\n'.join(out)+'\n'
if '--check' in sys.argv:assert target.read_text()==s
else:target.write_text(s)
(E/'NBL_AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=len(files)-(target in files),roots=roots),indent=2)+'\n')
print(len(roots),'printed roots')
