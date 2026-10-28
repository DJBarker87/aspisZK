"""Read-only native boundary inventory; never substitutes for a universal proof."""
from pathlib import Path
import subprocess,hashlib,json
E=Path('evidence/pv-batch2-20261027/batch2d')
base='73070ddd512bc4e79edfc0db714fb64dc74e87b8'
rows=[]
for name in ['weights.rs','sampler.rs','transport.rs']:
 p='crates/aspis-r1-cost-probe/src/'+name
 old=subprocess.check_output(['git','show',base+':'+p]);now=Path(p).read_bytes()
 rows.append(dict(path=p,frozen_sha256=hashlib.sha256(old).hexdigest(),current_sha256=hashlib.sha256(now).hexdigest(),identical=old==now))
assert all(r['identical'] for r in rows)
j=dict(frozen_base=base,original_sources=rows,changed_rust_paths=subprocess.check_output(['git','diff','--name-only','bcde8ada4f','--','crates','programs'],text=True).splitlines(),allocation=dict(frozen='Weights.materialize: powers7, heap::filled(1024,E::ZERO), Allocation error, iterator mutation',copied_caller='prepare_opening: heap::filled(1024,E::ZERO), Allocation error, fixed-array adapter, owned materialize',constructor='frozen Box allocation removed by copy; native effect correspondence remains open'),claims='source inventory only; no allocation trace, failure-independence, universal equality or ledger closure',rows_targeted=['V256','V257','V258','V259','V260'],rows_closed=[])
(E/'TRANSPORT-PREFLIGHT.json').write_text(json.dumps(j,indent=2)+'\n');print('original-source pins match; allocation transport remains open')
