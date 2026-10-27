from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rows=[]
p=Path('evidence/leaf-p6-9-20261027/LPi_L034/sources/LPi_generated/LPf_DotPushStep.lean');raw=p.read_text()
s=raw.replace('import LPf_DotWordStep','import FIo_NativeFuns\nimport FIo_ReduceBounds').replace('LPf_DotPushStep','LPn_DotPushStep')
(E/'LPn_DotPushStep.lean').write_text(s);rows.append({'path':str(p),'source_sha256':hashlib.sha256(raw.encode()).hexdigest(),'sha256':hashlib.sha256(s.encode()).hexdigest()})
parts=['import LPn_DotPushStep\nimport JGo_TX2_LoopChain\n']
for num,name in [(35,'LPf_DotPushFour'),(36,'LPf_DotPushCut')]:
 p=Path(f'evidence/leaf-p6-9-20261027/LPi_L{num:03}/sources/LPi_generated/{name}.lean');raw=p.read_text();s=re.sub(r'^import .*\n','',raw,flags=re.M).replace('LPf_DotPush','LPn_DotPush')
 parts.append(s);rows.append({'path':str(p),'source_sha256':hashlib.sha256(raw.encode()).hexdigest(),'sha256':hashlib.sha256(s.encode()).hexdigest()})
(E/'LPn_DotPushFour.lean').write_text('\n'.join(parts));(E/'LPn_DOT_COPIES.json').write_text(json.dumps({'repair':'imports/names only, literal proof bodies','sources':rows},indent=2)+'\n')
