"""Import-only B1 port of the accepted V228 fixed-array emission."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');raw=D/'raw132-resume2';out=D/'lean';record={}
for source,module in [('Types','PV_B3P_Types132'),('Funs','PV_B3P_Emission132')]:
 s=(raw/(source+'.lean')).read_text();p=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
 if source=='Funs':
  p=re.sub(r'^import PVB3P132Resume2-array.Types$','import PV_B3P_Types132',p,flags=re.M)
  names=re.findall(r'^def (\S+)',s,re.M)
  p+='\n'+''.join('#print axioms PV_B3P_132.'+n+'\n' for n in names)
  assert 'Array.update out count' in p and 'ok (out2, count2)' in p and 'cont (out1, count1, row1)' in p
  assert not re.search(r'index_mut|iter_mut|next_back|let \([^\n]*, _\)',p)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',p)
 (out/(module+'.lean')).write_text(p)
 record[module]=dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),ported_sha256=hashlib.sha256(p.encode()).hexdigest())
record.update(body_edits=False,edits=['Aeneas.Std/RustAttributes imports','private Types import','axioms print commands'],generated_resource_options_preserved=True,write_fidelity_scan='Array.update -> out2 -> (out1,count1) -> cont(out1,...) -> root result; no discarded backward continuation',native_emission_differential='not executed; formal loop/value correspondence remains OPEN')
(D/'port132-resume2.json').write_text(json.dumps(record,indent=2)+'\n')
