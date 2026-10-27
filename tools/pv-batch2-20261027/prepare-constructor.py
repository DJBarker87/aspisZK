from pathlib import Path
import re,json
E=Path('evidence/pv-batch2-20261027/extraction-weights/generated-252');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
t=(E/'Types.lean').read_text();f=(E/'Funs.lean').read_text()
(L/'PV_B2_WeightsTypes.lean').write_text(t+'\n'+''.join('#print axioms PV_B2_252.'+d+'\n' for d in re.findall(r'^(?:def|structure|inductive) ([\w.]+)',t,re.M)))
(L/'PV_B2_WeightsFuns.lean').write_text('-- API-only adaptation: the two emitted shift arguments31#i32 become31#u32.\n'+f.replace('31#i32','31#u32').replace('import PVB2252.Types','import R1Z.PV_B2_WeightsTypes')+'\n'+''.join('#print axioms PV_B2_252.'+d+'\n' for d in re.findall(r'^def ([\w.]+)',f,re.M)))
