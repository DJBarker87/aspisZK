from pathlib import Path
R=Path(__file__).resolve().parents[2];src=(R/'evidence/pv-canon-20261027/read-only/FullFuns.lean.txt').read_text();a=src.index('def host_sumcheck.prove_sumcheck_rounds\n');b=src.index('/-- [aspis_r1_cost_probe::host_semantic::semantic_row]',a)
s=src[a:b].replace('host_sumcheck.prove_sumcheck_rounds','checked_rounds').replace('host_sumcheck.prove_sumcheck_round ', 'checked_round ').replace('def host_sumcheck.prove_sumcheck\n','def checked_prover\n')
assert 'host_sumcheck.prove_sumcheck_round ' not in s
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_CheckedRounds.lean'
expected=('''import R1Z.PV_Canon_CheckedRound
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Proof-only monitored copies of the extracted recursion and entry.
Only the call of the monitored round replaces the original round. -/
'''+s+'''\nend R1Z.PV_Canon
''')

if '--check' in __import__('sys').argv:
 assert p.read_text()==expected, 'monitored recursion differs from generated body'
else:p.write_text(expected)
