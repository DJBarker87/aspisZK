from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029')
mods='Execution Ownership Drop Write Formatter Reporting Capture Joint Client Observer'.split()
rows=[]
for n in mods:
 m='PV_DIAG3_'+n;s=D/'source-inputs'/(m+'.lean.txt');p=D/'sources'/(m+'.lean');p.write_bytes(s.read_bytes());rows.append(dict(module=m,sha256=hashlib.sha256(s.read_bytes()).hexdigest(),authority='git tracked inherited diag3 source; compiled scratch removed'))
(D/'inherited-sources.json').write_text(json.dumps(rows,indent=2)+'\n')
