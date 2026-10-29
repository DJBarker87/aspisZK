from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';s=(P/'PV_RDB2C_SamplerInstance.lean').read_text();cut=s.index('section\n-- Unchanged source component: R1Z.ProverRwFullExternalTypes');text=s[:cut];(P/'PV_RDB2D_SamplerCore.lean').write_text(text)
(R/'evidence/pv-rdb2d-20261028/sampler-core.json').write_text(json.dumps(dict(parent='PV_RDB2C_SamplerInstance',parent_sha256=hashlib.sha256(s.encode()).hexdigest(),source_sha256=hashlib.sha256(text.encode()).hexdigest(),change='exact unchanged first three scoped source components; no native callback/dictionary definitions copied; no theorem text edited',components=['PV_B2_C_MachineArithmetic','PV_B2_C_SamplerEnvironment','PV_B2_E_GammaCohort']),indent=2)+'\n')
