"""Factor native continuation at the semantic-build return, without changing calls."""
from pathlib import Path
import textwrap,hashlib,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin55-20261029'
s=(L/'PV_RunJoin_NativeControl55.lean').read_text();a=s.index('                                let r15 ←');z=s.index('\n                              | core.ops.control_flow.ControlFlow.Break',a)
tail=textwrap.dedent(s[a:z]);tail=tail.replace('nonce_store1','store')
header='''import R1Z.PV_RunJoin_NativeControl55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterBuild55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
def run {A T : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (r14 : core.result.Result (host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) r1_wire.Error) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T) := do
'''
(L/'PV_RunJoin_NativeAfterBuild55.lean').write_text(header+textwrap.indent(tail,'  ')+'\n#print axioms run\nend R1Z.PV_RunJoin_NativeAfterBuild55\n')
body=s[s.index('def run {A'):s.index('\n#print axioms Phase')];a=body.index('                                let r15 ←');z=body.index('\n                              | core.ops.control_flow.ControlFlow.Break',a)
body=body[:a]+'''                                PV_RunJoin_NativeAfterBuild55.run publish public1 variant hash backend reserved context audit nonce_store1 r14'''+body[z:]
head='''import R1Z.PV_RunJoin_NativeAfterBuild55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeBuildContext55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
'''
(L/'PV_RunJoin_NativeBuildContext55.lean').write_text(head+body+'\n#print axioms run\nend R1Z.PV_RunJoin_NativeBuildContext55\n')
(E/'native-build-cut.json').write_text(json.dumps(dict(original_sha256=hashlib.sha256(s.encode()).hexdigest(),extracted_tail_sha256=hashlib.sha256(tail.encode()).hexdigest(),changes=['factor at actual build_with_material return','pass all live fields unchanged','rename only nonce_store1 to store']),indent=2)+'\n')
