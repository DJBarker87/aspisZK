"""Retain the exact current generic powers source, including terminal return."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
s=(e/'powers-Funs.lean.txt').read_text();b=s[s.index('/-- [aspis_r1_cost_probe::weights::powers]'):s.index('\nend ProverRwP6Powers')]
out='''import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev aspis_core.field.wide_exact.WideExact.ONE := ProverRwFull.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE
'''+b+'\nend R1Z.ProverRwP6PowersSource\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6PowersSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out);(e/'powers-source-map.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Import/namespace and same nominal Full carriers. Original ZERO/ONE/mul bindings, mutating array reads, wrapping index and early return all retained. No primitive success assumption.'),indent=2)+'\n')
