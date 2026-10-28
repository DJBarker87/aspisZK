from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
families={'KMX':('kani-mitig-20261028',list(range(48,54))),'NBH':('native-tx2d-20261027',list(range(2,8))),'NBU':('native-tx2j-20261028',[1,3,6,8,10,12,14,16,18,20,22,24,26,28])}
rows=[]
for prefix,(packet,ids) in families.items():
 for i in ids:
  p=E.parent/packet/f'{prefix}_K{i:03}'/'receipt.json';r=json.loads(p.read_text());c=r['command'];h=c[c.index('--harness')+1] if '--harness' in c else c[3]
  rows.append(dict(historical_attempt=r['attempt'],packet=packet,receipt=str(p.relative_to(E.parent.parent)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),harness=h,source_hashes=r['source_hashes'],status='PENDING reconstruction review'))
(E/'KNG_INVENTORY.json').write_text(json.dumps(rows,indent=2)+'\n')
