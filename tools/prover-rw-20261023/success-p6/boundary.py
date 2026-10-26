"""Literal unrolled boundary reference; native checks retained separately."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
s=(e/'boundary-flat-Funs.lean.txt').read_text();t=(e/'boundary-flat-Types.lean.txt').read_text()
b=s[s.index('/-- [prover_rw_success_p6::boundary_acc_step]'):s.index('\nend ProverRwP6BoundaryFlat')]
ty=t[t.index('structure BoundaryAcc'):t.index('\nend ProverRwP6BoundaryFlat')]
out='''import R1Z.ProverRwP6FlatTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundarySource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.M31.reduce_u64 := ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
abbrev aspis_core.field.CM31.new := ProverRwDictionaryBytes.Src.complex
'''+ty+'\n'+b+'\nend R1Z.ProverRwP6BoundarySource\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BoundarySource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out);(e/'boundary-flat-source-map.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),types_sha256=hashlib.sha256(t.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Import/namespace, nominal field carriers; retained current CT reduce64 and existing CM31.new source bindings. No arithmetic/array read removed. Current M31.reduce_u64 wrapper is M31(reduce64(x)); M31 is the retained U32 carrier.'),indent=2)+'\n')
