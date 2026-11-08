"""Change only imported modules and explicit roots in the retained strict driver."""
from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=['PV_LIB_SPEC_CallbackBound', 'PV_LIB_SPEC_CallbackHistory', 'PV_LIB_SPEC_CallbackModel', 'PV_LIB_SPEC_CallbackModelHistory', 'PV_LIB_SPEC_CallbackOperands', 'PV_LIB_SPEC_CallbackRecheck', 'PV_LIB_SPEC_CallbackRuntime', 'PV_LIB_SPEC_CallbackSource', 'PV_LIB_SPEC_CallbackStores', 'PV_LIB_SPEC_CallbackV2Runtime', 'PV_LIB_SPEC_NativeHistory', 'PV_LIB_SPEC_NativeModel', 'PV_LIB_SPEC_ThreadRepresentationGap', 'PV_LIB_SPEC_WordThreadArc', 'PV_LIB_SPEC_WordThreadRecheck', 'PV_LIB_SPEC_WordThreadRuntime']
base=(R/'lean/PV_LIB_SPEC_RawAuditSession10.lean').read_text()
start=base.index('    (#[`');end=base.index('\n  let env ←',start)
roots=[]
for m in modules:
 source=(R/'lean'/(m+'.lean')).read_text()
 declarations=re.findall(r'^(?:abbrev|def|theorem|inductive|structure) (\w+)',source,re.M)
 assert len(declarations)==len(set(declarations))
 roots.extend(m+'.'+n for n in declarations)
arrays='    (#[`'+', `'.join(modules)+'],\n     #[`'+', `'.join(roots)+'])'
new=base[:start]+arrays+base[end:]
(R/'lean/PV_LIB_SPEC_RawAuditSession11.lean').write_text(new)
report={'modules':modules,'roots':roots,'count':len(roots),'collector_suffix_sha256':hashlib.sha256(base[end:].encode()).hexdigest(),'driver_sha256':hashlib.sha256(new.encode()).hexdigest(),'walker_changes':False,'collector_changes':False}
(L/'SESSION11_RAW_ROOTS.json').write_text(json.dumps(report,indent=2)+'\n')
print('NEW roots:',len(roots))
