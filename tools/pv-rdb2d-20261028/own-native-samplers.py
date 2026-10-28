from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';records=[]
mapping={'R1Z.PV_B2_C_SamplerEnvironment':'R1Z.PV_RDB2D_SamplerCore','R1Z.PV_B2_E_GammaCohort':'R1Z.PV_RDB2D_SamplerCore','R1Z.ProverRwFullTypes':'R1Z.PV_RDB2D_ProverRwFullTypes','R1Z.ProverRwFullExternalFuns':'R1Z.PV_RDB2D_ProverRwFullExternalFuns','R1Z.PV_B2_E_OrdinaryOriginal':'R1Z.PV_RDB2D_OrdinaryOriginal','R1Z.PV_B2_E_Install250':'R1Z.PV_RDB2D_Install250'}
for old,new in [('PV_B2_E_OrdinaryOriginal','PV_RDB2D_OrdinaryOriginal'),('PV_B2_E_Install250','PV_RDB2D_Install250'),('PV_B2_E_GammaOriginal','PV_RDB2D_GammaOriginal')]:
 raw=(P/(old+'.lean')).read_text();s=re.sub(r'^import (\S+)',lambda x:'import '+mapping.get(x[1],x[1]),raw,flags=re.M);assert re.sub(r'^import .*\n','',raw,flags=re.M)==re.sub(r'^import .*\n','',s,flags=re.M);(P/(new+'.lean')).write_text(s);records.append(dict(original=old,module='R1Z/'+new,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),owned_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='imports only; every dictionary, callback, statement and proof body unchanged'))
(R/'evidence/pv-rdb2d-20261028/native-sampler-components.json').write_text(json.dumps(records,indent=2)+'\n')
