"""Import/metadata-only port of the accepted four-slot V241 continuation."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');raw=D/'raw224-resume3';record={}
for source,module in [('Types','PV_B3P_Types224'),('Funs','PV_B3P_Emission224')]:
 s=(raw/(source+'.lean')).read_text();p=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
 p=p.replace('@[discriminant isize]\n','')
 if source=='Funs':
  p=p.replace('import PVB3P224Resume3FourSlots.Types','import PV_B3P_Types224')
  assert p.count('31#i32')==2
  p=p.replace('31#i32','31#u32')
  p+='\n'+''.join('#print axioms PV_B3P_224.'+n+'\n' for n in re.findall(r'^def (\S+)',s,re.M))
  assert 'Array.update helper r val' in p and 'cont (helper1, r2)' in p
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',p)
 assert not re.search(r'index_mut|iter_mut|next_back|let \([^\n]*, _\)',p)
 (D/'lean'/(module+'.lean')).write_text(p)
 record[module]=dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),ported_sha256=hashlib.sha256(p.encode()).hexdigest())
record.update(body_edits=False,edits=['Aeneas.Std/RustAttributes imports','private Types import','two positive31 shift-argument type ports i32 -> u32, value31 unchanged, PV_B3P_Shift224.shift31_value','remove unsupported discriminant metadata only; no discriminant operation reached; constructor order and payloads unchanged','axioms print commands'],generated_resource_options_preserved=True,write_fidelity_scan='Array.update helper r val -> helper1 -> cont(helper1,r2) -> returned helper; no discarded backward continuation',scope='helper continuation only; trace/registry prefix still open')
(D/'port224-resume3.json').write_text(json.dumps(record,indent=2)+'\n')
