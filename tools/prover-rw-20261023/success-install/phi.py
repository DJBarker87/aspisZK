"""Literal generic four-point inverse owner with nominal CodeField rebind."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/v8-r0-zk-20261009/lean/AspisR1ProducerRelease47/EncoderGeneric54.lean';s=p.read_text()
m=re.search(r'^def generic54.phi_inverse\b',s,re.M);end=s.index('\ndef ',m.end());b=s[m.start():end].strip()
t='''import R1Z.ProverRwSuccessHashes
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwSuccessPhiSource
'''+b.replace('scalar.CodeField','aspis_core.r0.scalar.CodeField')+'\nend R1Z.ProverRwSuccessPhiSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessPhiSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-install/phi-source.json').write_text(json.dumps(dict(path=str(p.relative_to(r)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declaration_sha256=hashlib.sha256(b.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),rewrites='Only nominal CodeField carrier qualification; full callback order and result constructors unchanged.'),indent=2)+'\n')
print(t)
