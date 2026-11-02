"""One positive assembly missing from the peer mutation-test output."""
from pathlib import Path
import sys,json,subprocess,time
E=Path(__file__).resolve().parent;W=Path('/private/tmp/NEO_peer_review_20261102')
P=W/'evidence/slice-q-mul2-20261101';assert P.exists()
code=f'''from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
sys.path.insert(0,{str(P)!r})
import NEI_composition as c
base=c.obj(c.E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
edges=c.prepare(base);out,delta=c.validate(base,edges)
closed=[r for r in out['rows'] if r['composed_status']=='CLOSED']
assert sorted(r['row'] for r in closed)==sorted(['TX1:049','TX1:110','TX1:192','TX1:194','TX2:032','TX2:076','TX2:120','TX2:123','TX2:125','TX1:107','TX1:195','TX2:073','TX2:101','TX1:177'])
Path({str(E/'NEO_PEER_POSITIVE.json')!r}).write_text(json.dumps(dict(delta=delta,rows=closed,edges=[e for e in edges['edges'] if e['status']=='CLOSED'],row_certificates=edges['row_certificates']),indent=1)+'\\n')
print(json.dumps(delta))
'''
start=time.monotonic()
r=subprocess.run([sys.executable,'-c',code],cwd=W,text=True,capture_output=True)
(E/'NEO_PEER_POSITIVE.stdout').write_text(r.stdout);(E/'NEO_PEER_POSITIVE.stderr').write_text(r.stderr)
(E/'NEO_PEER_POSITIVE_RECEIPT.json').write_text(json.dumps(dict(exit_status=r.returncode,wall_seconds=time.monotonic()-start,command='NEI_composition.validate(NDT baseline, NEI_composition.prepare(baseline))',source_revision='1dbf5ad1511b14687a27a2e5043ed50a8515547c',prover_runs=0),indent=1)+'\n')
print(r.stdout[-1200:]+r.stderr[-1200:]);sys.exit(r.returncode)
