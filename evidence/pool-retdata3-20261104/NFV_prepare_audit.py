from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata2-20261104'
modules=['NFV_Accounts','NFV_HelperModel','NFV_Copy','NFV_ListFrames','NFV_Envelope','NFV_RequestWindows','NFV_RequestOracle','NFV_RequestIndexes','NFV_RequestGuards','NFV_PoolReturnData']
roots={
'NFV_Accounts':['keys','flags','account_order'],
'NFV_HelperModel':['success','rejected','erase','same_emission'],
'NFV_Copy':['range','prefix_copy','suffix','update','bind_pair_finish','range_then','prefix_then','suffix_then'],
'NFV_ListFrames':['set_next','copy_next','copy_at'],
'NFV_Envelope':['emitted','header_value','pure_value'],
'NFV_RequestWindows':['complete','envelope'],
'NFV_RequestOracle':['erase','profile_rejected'],
'NFV_RequestIndexes':['window','header','profile','release','program','payment'],
'NFV_RequestGuards':['lists','array','zero_binding']}
root_names=[m+'.'+n for m,ns in roots.items() for n in ns]
(E/'NFV_AUDIT_PLAN.json').write_text(json.dumps(dict(modules=modules,own_roots=root_names,total_roots=69+len(root_names)),indent=1)+'\n')
base=(O/'NFR_Driver.lean').read_text();s=base
s=s.replace('(#[`NFR_AfterstateForward,','(#['+','.join('`'+m for m in modules)+',`NFR_AfterstateForward,',1)
s=s.replace('#[`NFR_AfterstateForward.self_ne,','#['+','.join('`'+n for n in root_names)+',`NFR_AfterstateForward.self_ne,',1)
(E/'NFV_Driver.lean').write_text(s)
(E/'NFV_DRIVER.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='NFR_Driver.lean',tofile='NFV_Driver.lean')))
s=(O/'NFR_Coherence.lean').read_text().replace('NFR_Coherence','NFV_Coherence').replace('NFR_LOADED.jsonl','NFV_LOADED.jsonl').replace('loaded NFR closure','loaded NFV and inherited NFR closure')
s=s.replace('let env ← importModules #[','let env ← importModules #['+','.join('{module := `'+m+', importAll := true}' for m in modules)+',',1)
(E/'NFV_Coherence.lean').write_text(s)
walker=O/'NFR_WALKER.lean';assert hashlib.sha256(walker.read_bytes()).hexdigest()=='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
(E/'NFV_WALKER_PIN.json').write_text(json.dumps(dict(path=str(walker),sha256=hashlib.sha256(walker.read_bytes()).hexdigest(),byte_identical_to_NEP=True,driver_diff='NFV_DRIVER.diff',fixtures_required=True),indent=1)+'\n')
