import json,sys
from pathlib import Path
H=Path(sys.argv[1]);expected={'transfer-13':(1197177,1138518),'transfer-255':(1199286,1169558),'transfer-1023':(1193428,1169306),'withdrawal-13':(1193569,1148816),'withdrawal-255':(1193699,1178769),'withdrawal-1023':(1195178,1176341)}
rows=[json.loads(l) for l in (H/'sweep/control/sweep.jsonl').read_text().splitlines()]
assert len(rows)==6
for r in rows:
 assert r['outcome']=='accepted' and r['exit_status']==0,r
 assert (r['stage1_cu'],r['settlement_cu'])==expected[r['label'].removeprefix('control-')],r
print('Six controls reproduce frozen pins exactly')
