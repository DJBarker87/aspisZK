"""Read-only development status probe; no prover invocation."""
import sys,time,json
from pathlib import Path
R=Path(__file__).resolve().parents[2]
for d in ['ledger4-20261102','slice-q-compose2-20261102','slice-q-compose3-20261102','slice-q-mul2-20261101','slice-s-compose5-20261102','slice-s-compose6-20261102','slice-s-compose7-20261103','slice-s-compose8-20261104']:
 sys.path.insert(0,str(R/'evidence'/d))
import NEN_validate as n,NEO_validate as o,NET_validate as t,NEM_validate as m,NEQ_validate as q,NEU_validate as u,NEX_validate as x
base=o.baseline();print('baseline',len(base['rows']),flush=True)
for v in [m,q,u,x]:
 s=time.monotonic();out=v.compose(n.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),v.read(v.E/(v.__name__[:3]+'_LEDGER_DELTA.json')),v.read(v.E/(v.__name__[:3]+'_REVIEWED_CERTIFICATES.json')))
 print(v.__name__,sum(r['composed_status']=='CLOSED' for r in out['rows']),time.monotonic()-s,flush=True)
print('NET',t.validate(),flush=True)
