from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
mods=[];roots=[];pins={}
for p in sorted(Path('lean').glob('NBA_*.lean')):
 if p.stem=='NBA_Audit':continue
 s=p.read_text();ns=re.findall(r'^namespace (\S+)',s,re.M);assert len(ns)==1,(p,ns)
 declared=re.findall(r'^(?:private )?theorem\s+([^\s{(:]+)',s,re.M)
 printed=re.findall(r'^#print axioms (\S+)',s,re.M)
 assert set(declared)==set(printed),(p,declared,printed)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M),p
 mods.append(p.stem);roots.extend(ns[0]+'.'+n for n in printed)
 pins[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
Path('lean/NBA_Audit.lean').write_text(''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#print axioms '+r+'\n' for r in roots))
(E/'NBA_AUDIT_PLAN.json').write_text(json.dumps(dict(modules=mods,roots=roots,source_sha256=pins),indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots))))
