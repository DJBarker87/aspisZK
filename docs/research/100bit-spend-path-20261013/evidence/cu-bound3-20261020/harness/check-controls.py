import json,sys
from pathlib import Path
H=Path(sys.argv[1]);expected={'transfer-13':(1196046,1135481),'transfer-255':(1198152,1166524),'transfer-1023':(1192314,1166269),'withdrawal-13':(1192444,1145777),'withdrawal-255':(1192575,1175735),'withdrawal-1023':(1194056,1173313)}
rows=[json.loads(l) for l in (H/'sweep/control/sweep.jsonl').read_text().splitlines()]
assert len(rows)==6
for r in rows:
 assert r['outcome']=='accepted' and r['exit_status']==0,r
 assert (r['stage1_cu'],r['settlement_cu'])==expected[r['label'].removeprefix('control-')],r
print('Six controls reproduce adopted pins exactly')
