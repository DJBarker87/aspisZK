import json,sys
from pathlib import Path
H=Path(sys.argv[1]);expected={'transfer-13':(1196707,1136739),'transfer-255':(1198819,1167782),'transfer-1023':(1192970,1167530),'withdrawal-13':(1193098,1147040),'withdrawal-255':(1193225,1176995),'withdrawal-1023':(1194707,1174566)}
rows=[json.loads(l) for l in (H/'sweep/control/sweep.jsonl').read_text().splitlines()]
assert len(rows)==6
for r in rows:
 assert r['outcome']=='accepted' and r['exit_status']==0,r
 assert (r['stage1_cu'],r['settlement_cu'])==expected[r['label'].removeprefix('control-')],r
print('Six controls reproduce candidate CU exactly')
