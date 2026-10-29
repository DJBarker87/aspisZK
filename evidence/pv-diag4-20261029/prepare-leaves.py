from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');pins=[]
for n in ['Execution','Ownership','Drop','Capture']:
 m='PV_DIAG3_'+n;s=D/'source-inputs'/(m+'.lean.txt');out=D/'sources'/(m+'.lean');out.write_bytes(s.read_bytes());pins.append(dict(module=m,sha256=hashlib.sha256(s.read_bytes()).hexdigest(),reason='inherited compiled scratch removed by prior job; fresh dependency for concrete leaf law'))
(D/'leaf-dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
