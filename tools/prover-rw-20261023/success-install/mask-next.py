"""Retain mask helper's complete checked extraction, with nominal field aliases.
No claim about current wrapping arithmetic/native association is made here.
"""
from pathlib import Path
import re,hashlib,json,sys
r=Path(__file__).resolve().parents[3];p=r/'docs/research/100bit-spend-path-20261013/evidence/current-selected-mask-extraction-20261015/mask-funs-a.source.lean';s=p.read_text();blocks=[];pins={}
for m in re.finditer(r'\bdef\s+([\w.]+)(?=\s|\{)',s):
 n=m[1]
 if n.startswith('extraction_probe.'):continue
 b=s[m.start():s.index('\n/--',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest();blocks.append(b)
t='''import R1Z.ProverRwSuccessHeapInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessMaskSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev field.M31 := ProverRwFull.aspis_core.field.M31
abbrev field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev field.PreparedQm31Multiplier.mul.closure := Unit
structure field.PreparedQm31Multiplier where
  components : Array (Array field.M31 3#usize) 3#usize
abbrev field.PreparedQm31Multiplier.new.closure := Unit
'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessMaskSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessMaskSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t);(r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next/mask-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='Nominal carrier aliases and local prepared representation only; checked arithmetic retained verbatim. Current native wrapping/checked association is NOT proved.'),indent=2)+'\n')
