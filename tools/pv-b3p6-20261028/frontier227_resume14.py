"""Retain raw extraction; generate only an explicit callee-parameter port.
Never compile the extractor's external-axiom template.
"""
from pathlib import Path
import hashlib,json,re
import sys
if '--check' in sys.argv:
 def checked_write(path, data, *args, **kwargs):
  assert path.read_text() == data, ('generator drift',str(path))
  return len(data)
 Path.write_text = checked_write
D=Path('evidence/pv-b3p6-20261028');R=D/'resume14/frontier-raw';L=D/'lean'
s=(R/'Types.lean').read_text();s=s.replace('import Aeneas\n','import Aeneas.Std\n').replace('@[discriminant isize, rust_type "aspis_core::state_only_prefix::r0::Error"]','@[rust_type "aspis_core::state_only_prefix::r0::Error"]')
(L/'PV_B3P_Frontier14Types.lean').write_text(s)
s=(R/'Funs.lean').read_text().replace('import Aeneas\n','import Aeneas.Std\n').replace('import Missing14.Types','import PV_B3P_Frontier14Types').replace('import Missing14.FunsExternal\n','')
# Aeneas's emitted template declares exactly this signature. It becomes a
# quantified input, never an axiom/stub. The frontier body text is untouched.
param='''
variable (fields : alloc.vec.Vec Std.U8 → Slice aspis_core.field.M31 →
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × alloc.vec.Vec Std.U8))
'''
s=s.replace('namespace PV_B3P_Missing14Frontier\n','namespace PV_B3P_Missing14Frontier\n'+param)
s+='\n#print axioms PV_B3P_Missing14Frontier.frontier\n'
(L/'PV_B3P_Frontier14Port.lean').write_text(s)
body=lambda s:s[s.index('  := do\n'):s.rindex('\nend PV_B3P_Missing14Frontier')]
assert body(s)==body((R/'Funs.lean').read_text())
record=dict(raw_sha256=hashlib.sha256((R/'Funs.lean').read_bytes()).hexdigest(),port_sha256=hashlib.sha256(s.encode()).hexdigest(),body_byte_identical=True,changes=['imports','discriminant attribute metadata in type port','opaque fields declaration becomes explicit quantified callee port, retaining exact signature'],external_template_compiled=False,scope='Exact caller body extraction with explicit fields dependency; no axiom and no fields extraction credit.')
(D/'resume14/frontier-port.json').write_text(json.dumps(record,indent=2)+'\n')
