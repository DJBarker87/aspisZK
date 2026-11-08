"""Reuse unchanged strict private-import walker, changing root inputs only."""
from pathlib import Path
import re,json
E=Path('evidence/pv-lib-20261107/lane-A')
modules=['PV_LIB_A_NativeLeaves','PV_LIB_A_Unique612','PV_LIB_A_UniqueBinding','PV_LIB_A_SourceWriters','PV_LIB_A_PureCalls','PV_LIB_A_PurePoll','PV_LIB_A_PureValues','PV_LIB_A_WriterNative','PV_LIB_A_Numbering','PV_LIB_A_TypedDrop178','PV_LIB_A_Range165','PV_LIB_A_Residual280']
roots=[]
for m in modules:
 s=Path('lean',m+'.lean').read_text()
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):roots.append(m+'.'+n)
s=Path('lean/PV_LIB_RawAudit2.lean').read_text()
a=s.index('  let (modules, roots) :=');b=s.index('  let env ←',a)
s=s[:a]+'  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'+s[b:]
Path('lean/PV_LIB_A_RawAudit.lean').write_text(s)
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,driver='PV_LIB_A_RawAudit',provenance='PV_LIB_RawAudit2 source: unchanged walker/collector body, only modules and roots arrays replaced'),indent=2)+'\n')
print(len(roots),'new roots')
