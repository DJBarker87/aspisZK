"""Literal extracted flat serialization, with existing limb source binding."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
s=(e/'flat-Funs.lean.txt').read_text();b=s[s.index('/-- [prover_rw_success_p6::wide_bytes_flat]'):s.index('\nend ProverRwP6Flat')]
h='''import R1Z.ProverRwP6TransitionInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6FlatSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.wide_exact.WideExact.to_limbs := ProverRwDictionaryBytes.Src.limbs
'''
out=h+b+'\nend R1Z.ProverRwP6FlatSource\n';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6FlatSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out);(e/'flat-source-map.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Import/namespace and existing nominal wide carrier/retained to_limbs source. All native byte conversion and 40 array reads retained.'),indent=2)+'\n')
