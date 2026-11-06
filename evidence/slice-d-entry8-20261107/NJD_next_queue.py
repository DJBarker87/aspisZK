from NJD_transport import *
import time
while True:
 rows=[json.loads(s) for s in (E/'NJD_ATTEMPTS.jsonl').read_text().splitlines()]
 if any(r['attempt']=='NJD_K017' for r in rows):break
 time.sleep(5)
from NJD_formal import run
for a,m in [('NJD_L003','NJD_Trace'),('NJD_L004','NJD_GuardCuts'),('NJD_L005','NJD_EntrySpine')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m+' before dependency chain')
