"""Port only imports and unsupported discriminant metadata; preserve raw output."""
from pathlib import Path
import hashlib,json
D=Path('evidence/pv-b3p6-20261028'); O=D/'resume13';L=D/'lean';out=[]
for kind in ['Types','Funs']:
 p=O/'missing-semantic'/(kind+'.lean');s=p.read_text();s=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n').replace('import Missing13.Types','import PV_B3P_MissingSemantic13Types')
 s=s.replace('@[discriminant isize]\n','')
 # Exact raw declarations; only metadata and imports change.
 mod='PV_B3P_MissingSemantic13'+kind;(L/(mod+'.lean')).write_text(s)
 out.append(dict(module=mod,raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),ported_sha256=hashlib.sha256(s.encode()).hexdigest(),changes=['Aeneas.Std / RustAttributes imports','private Types module path','unsupported discriminant metadata removed, constructors unchanged'],body_edits=[]))
(O/'semantic-port.json').write_text(json.dumps(out,indent=2)+'\n')
