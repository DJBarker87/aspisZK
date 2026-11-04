from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';audits=[]
for n in [78297,78298,78299]:
 j=json.load(open(E/f'lean-{n}/receipt.json'));assert j['exit']==0 and j['swap']=='0'
 assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256']
 audits.append(j)
snapshot=json.load(open(E/audits[-1]['dependencies_snapshot']))
(E/'release-object-inputs.json').write_text(json.dumps(dict(audits=audits,final_launch_dependencies=snapshot['objects']),indent=2)+'\n')
print('Prepared three successful release source/object records and final-launch dependency addendum')
