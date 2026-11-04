from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata2-20261104'
base=(O/'NFR_Driver.lean').read_text();s=base
s=s.replace('(#[`NFR_AfterstateForward,','(#[`NFV_Accounts,`NFV_HelperModel,`NFV_PoolReturnData,`NFR_AfterstateForward,',1)
s=s.replace('#[`NFR_AfterstateForward.self_ne,','#[`NFV_HelperModel.success,`NFV_HelperModel.rejected,`NFV_HelperModel.erase,`NFV_HelperModel.same_emission,`NFV_Accounts.keys,`NFV_Accounts.flags,`NFV_Accounts.account_order,`NFR_AfterstateForward.self_ne,',1)
(E/'NFV_Driver.lean').write_text(s)
(E/'NFV_DRIVER.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='NFR_Driver.lean',tofile='NFV_Driver.lean')))
s=(O/'NFR_Coherence.lean').read_text().replace('NFR_Coherence','NFV_Coherence').replace('NFR_LOADED.jsonl','NFV_LOADED.jsonl').replace('loaded NFR closure','loaded NFV and inherited NFR closure')
s=s.replace('let env ← importModules #[','let env ← importModules #[{module := `NFV_Accounts, importAll := true},{module := `NFV_HelperModel, importAll := true},{module := `NFV_PoolReturnData, importAll := true},',1)
(E/'NFV_Coherence.lean').write_text(s)
walker=O/'NFR_WALKER.lean';assert hashlib.sha256(walker.read_bytes()).hexdigest()=='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
(E/'NFV_WALKER_PIN.json').write_text(json.dumps(dict(path=str(walker),sha256=hashlib.sha256(walker.read_bytes()).hexdigest(),byte_identical_to_NEP=True,driver_diff='NFV_DRIVER.diff',fixtures_required=True),indent=1)+'\n')
