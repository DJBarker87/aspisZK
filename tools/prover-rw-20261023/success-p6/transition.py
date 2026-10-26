"""Exact current transition bodies with explicit nominal input transport."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
s=(e/'transition-Funs.lean.txt').read_text();t=(e/'transition-Types.lean.txt').read_text()
names=['aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant','aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1','aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1','aspis_statement.pool_v1.pair_forest_semantic_terminal.SemanticPublic','aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public']
blocks=[]
for name in names:
 m=re.search(r'^(?:structure|inductive) '+re.escape(name)+r'\b',t,re.M);assert m,name
 end=t.find('\n/--',m.end());end=end if end>=0 else t.index('\nend ProverRwDirectTransition',m.end())
 b=t[m.start():end].strip();blocks.append(b)
body=s[s.index('/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public]'):s.index('\nend ProverRwDirectTransition')]
out='''import R1Z.ProverRwSuccessNativeWideInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6TransitionSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes]
'''+ '\n\n'.join(blocks)+'\n'+body+'\nend R1Z.ProverRwP6TransitionSource\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6TransitionSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out);(e/'transition-source-map.json').write_text(json.dumps(dict(functions_sha256=hashlib.sha256(s.encode()).hexdigest(),types_sha256=hashlib.sha256(t.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Imports/namespace, retaining raw payment/semantic/Public carriers; existing field/Late structures nominally reused. No field accessor callback or value-equivalence premise.'),indent=2)+'\n')
