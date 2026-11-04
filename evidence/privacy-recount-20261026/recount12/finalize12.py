from pathlib import Path
import json
P=Path(__file__).resolve().parent
m=json.loads((P/'manifest.json').read_text());pins=json.loads((P/'pins.json').read_text())
for x in m:
 if x['ref']=='rw' and x['revision']!=pins['revisions']['rw']:x['ref']='rw-local'
(P/'manifest.json').write_text(json.dumps(m,indent=1)+'\n');by={x['ref']+':'+x['path']:x for x in m}
x=json.loads((P/'definition-audit12.json').read_text())
for row in x:
 for label in ['sources','changed']:
  row[label]=[dict(by[z['ref']+':'+z['path']],prior_identical=z['prior_identical']) for z in row[label]]
(P/'definition-audit12.json').write_text(json.dumps(x,separators=(',',':'))+'\n')
