"""Change only imported modules and explicit roots in the retained strict driver."""
from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=['PV_LIB_SPEC_AllocationImages','PV_LIB_SPEC_AllocationSites','PV_LIB_SPEC_SiteArc','PV_LIB_SPEC_InitImageRecheck','PV_LIB_SPEC_SiteRuntime','PV_LIB_SPEC_SiteArcRecheck','PV_LIB_SPEC_SiteV2Runtime','PV_LIB_SPEC_SiteHistory','PV_LIB_SPEC_CallbackImageGap','PV_LIB_SPEC_CallbackNativeGap']
base=(R/'lean/PV_LIB_SPEC_RawAuditSession9.lean').read_text()
start=base.index('    (#[`');end=base.index('\n  let env ←',start)
roots=[]
for m in modules:
 source=(R/'lean'/(m+'.lean')).read_text()
 declarations=re.findall(r'^(?:abbrev|def|theorem|inductive|structure) (\w+)',source,re.M)
 assert len(declarations)==len(set(declarations))
 roots.extend(m+'.'+n for n in declarations)
arrays='    (#[`'+', `'.join(modules)+'],\n     #[`'+', `'.join(roots)+'])'
new=base[:start]+arrays+base[end:]
(R/'lean/PV_LIB_SPEC_RawAuditSession10.lean').write_text(new)
report={'modules':modules,'roots':roots,'count':len(roots),'collector_suffix_sha256':hashlib.sha256(base[end:].encode()).hexdigest(),'driver_sha256':hashlib.sha256(new.encode()).hexdigest(),'walker_changes':False,'collector_changes':False}
(L/'SESSION10_RAW_ROOTS.json').write_text(json.dumps(report,indent=2)+'\n')
print('NEW roots:',len(roots))
