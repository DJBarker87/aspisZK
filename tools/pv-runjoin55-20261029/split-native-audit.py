"""Split at successful audit before salts/domain/backend initialization."""
from pathlib import Path
import textwrap
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RunJoin_NativeBuildContext55.lean').read_text();a=s.index('                          let i2 ←');z=s.index('\n                        else',a)
tail=textwrap.dedent(s[a:z])
for x,y in [('nonce_store1','store'),('noised_c11','noised'),('val1.mask_only_c1','maskOnly'),('val4','d')]:tail=tail.replace(x,y)
header='''import R1Z.PV_RunJoin_NativeAfterBuild55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterAudit55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
def run {A T0 : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
    (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g h1_padding : Array aspis_core.field.QM31 1024#usize)
    (audit : prover.MaskedFixtureAudit) (store : T0) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T0) := do
'''
(L/'PV_RunJoin_NativeAfterAudit55.lean').write_text(header+textwrap.indent(tail,'  ')+'\n#print axioms run\nend R1Z.PV_RunJoin_NativeAfterAudit55\n')
body=s[s.index('def run {A'):s.index('\n#print axioms run')];a=body.index('                          let i2 ←');z=body.index('\n                        else',a)
body=body[:a]+'''                          PV_RunJoin_NativeAfterAudit55.run publish aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised_c11 val1.mask_only_c1 val4 g h1_padding audit nonce_store1'''+body[z:]
head='''import R1Z.PV_RunJoin_NativeAfterAudit55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAuditContext55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
'''
(L/'PV_RunJoin_NativeAuditContext55.lean').write_text(head+body+'\n#print axioms run\nend R1Z.PV_RunJoin_NativeAuditContext55\n')
