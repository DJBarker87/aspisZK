from run import H
from pathlib import Path
import re,json
s=(H/'lean-61598/receipt/stdout.log').read_text()
xs=list(re.finditer(r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s,re.M));bad=[]
for m in xs:
 ax={a.strip()for a in (m[2]or'').split(',')if a.strip()}
 if ax-{'propext','Classical.choice','Quot.sound'}:bad.append((m[1],sorted(ax)))
assert len(xs)==83 and not bad,(len(xs),bad)
(H/'audit83-resume7.json').write_text(json.dumps(dict(attempt=61598,audited=83,bad=bad),indent=2)+'\n')
print(json.dumps(dict(audited=83,bad=bad)))
