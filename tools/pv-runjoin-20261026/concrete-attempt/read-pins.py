"""Read committed sibling heads and exact declarations; no checkout or writes there."""
import subprocess,json,hashlib
from pathlib import Path
out=Path('evidence/pv-runjoin-20261026/concrete-attempt')
refs=['codex/cx-prover-rw-20261023','codex/pv-cb-20261026','codex/cx-prover-dict-20261026','codex/cx-ct-kernels-v2-20261022']
rows=[]
for ref in refs:
    rev=subprocess.check_output(['git','rev-parse',ref],text=True).strip()
    log=subprocess.check_output(['git','log','-1','--format=%h %s',ref],text=True).strip()
    rows.append(dict(branch=ref,revision=rev,log=log))
(out/'sibling-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
files={
'codex/cx-prover-dict-20261026':['PDict_StoreTransport','PDict_FallibleTransport','PDict_FormatterStoreMap'],
'codex/pv-cb-20261026':['PV_CB_Composition','PV_CB_Independent'],
'codex/cx-prover-rw-20261023':['ProverRwSuccessBodyInterpretation']}
for ref,names in files.items():
    rev=next(r['revision'] for r in rows if r['branch']==ref)
    for name in names:
        path=f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean'
        raw=subprocess.check_output(['git','show',f'{rev}:{path}'])
        (out/(name+'.lean.txt')).write_bytes(raw)
