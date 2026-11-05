"""Independent source import baselines and explicit new theorem roots."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
names=['NHQ_Tx2CommonModel','NHQ_Tx2AuthModel','NHQ_FinishRelationModel','NHQ_PacketPorts','NHQ_RoundDomain','NHQ_WeightPort','NHQ_FinishPackets','NHQ_FinishFrames','NHQ_QueryFrame']
roots=[]
for name in names:
 p=E/(name+'.lean')
 roots += [name+'.'+x for x in re.findall(r'^theorem (\w+)',p.read_text(),re.M)]
(E/'NHQ_AUDIT_ROOTS.json').write_text(json.dumps({'groups':[roots]},indent=1)+'\n')
base={};pins={}
for src in ['candidate-prepare-20261106/NHF_EXPECTED_IMPORTS.jsonl','slice-d-finish3-20261106/NHE_EXPECTED_IMPORTS.jsonl','pool-retarget-20261105/NGK_EXPECTED_IMPORTS.jsonl','carriers-bind-20261105/NGS_EXPECTED_IMPORTS.jsonl','history-persist-20261105/NGR_EXPECTED_IMPORTS.jsonl']:
 p=E.parent/src
 if not p.exists():continue
 pins[str(p.relative_to(E.parent))]=hashlib.sha256(p.read_bytes()).hexdigest()
 for l in p.read_text().splitlines():
  row=json.loads(l)
  if row['module'] in base and base[row['module']]['imports']!=row['imports']:raise ValueError('incompatible independent baselines: '+row['module'])
  base[row['module']]=row
for p in E.glob('NHQ_*.lean'):
 base[p.stem]={'module':p.stem,'imports':['Init']+re.findall(r'^import (\w+)',p.read_text(),re.M)}
(E/'NHQ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in base.values()))
(E/'NHQ_IMPORT_BASELINES.json').write_text(json.dumps(pins,indent=1)+'\n')
print(json.dumps(dict(roots=len(roots),baselines=len(base))))
