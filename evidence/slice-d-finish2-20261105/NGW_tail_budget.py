from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text())for p in E.glob('NGW_[KLE][0-9][0-9][0-9]/receipt.json')]
used={kind:sum(r['attempt'].startswith(p)for r in rows)for kind,p in [('kani','NGW_K'),('lean_audit','NGW_L'),('extraction','NGW_E')]}
(E/'NGW_BUDGET.json').write_text(json.dumps(dict(limit=dict(kani=100,lean_audit=80,extraction=3),used=used,unused_ids={kind:[i for i in range(1,n+1)if not any(r['attempt']==f'NGW_{p}{i:03d}'for r in rows)]for kind,p,n in [('kani','K',100),('lean_audit','L',80),('extraction','E',3)]},method='Every launcher receipt charged, including own preflight failures. No unchanged timeout/memory resubmission. Full budget work continues.'),indent=2)+'\n');print(used)
