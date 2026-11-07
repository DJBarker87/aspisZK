"""New roots only; unchanged strict raw walker/collector from the accepted driver."""
from pathlib import Path
import json,re
E=Path('evidence/pv-lib-20261107/lane-A/session4')
modules=['PV_LIB_A_OwnerStore','PV_LIB_A_OwnerStoreTransport','PV_LIB_A_WriterSites','PV_LIB_A_OwnerStoreActions','PV_LIB_A_RangeWriter','PV_LIB_A_WriterNumbering','PV_LIB_A_Caller124','PV_LIB_A_NameValidity','PV_LIB_A_PrefixTransport']
roots=[]
for m in modules:
 s=Path('lean',m+'.lean').read_text()
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):roots.append(m+'.'+n)
s=Path('lean/PV_LIB_RawAudit2.lean').read_text();a=s.index('  let (modules, roots) :=');b=s.index('  let env ←',a)
s=s[:a]+'  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'+s[b:]
Path('lean/PV_LIB_A_RawAudit4.lean').write_text(s)
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,driver='PV_LIB_A_RawAudit4',provenance='PV_LIB_RawAudit2 unchanged walker/collector; only module and root arrays differ'),indent=2)+'\n')
print(len(roots),'new roots')
