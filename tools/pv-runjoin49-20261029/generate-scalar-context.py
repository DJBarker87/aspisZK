"""Expose only the two scalar calls; retain all other source calls and branches."""
from pathlib import Path
import json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin49-20261029'
s=(L/'PV_RunJoin_PrepareMaterialContext49.lean').read_text();body=s[s.index('def run\n'):s.index('\n\ntheorem source')]
params=body[:body.index(' :\n  Result (core.result.Result prover.PreparedOpening verifier.Error)')]
scalar='''
  (scalar : host_transcript.Transcript aspis_core.digest.LegacyHashFn → U8 → Slice U8 → Bool →
    Result (aspis_core.field.wide_exact.WideExact × host_transcript.Transcript aspis_core.digest.LegacyHashFn))'''
body=body.replace(params,params+scalar,1)
pattern=r'host_transcript.Transcript.scalar\n\s+aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32'
body,count=re.subn(pattern,'scalar',body);assert count==2
source=params.replace('def run','theorem source',1)+''' :
    PV_RunJoin_PrepareMaterialContext49.run variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail=
      run variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail
        (host_transcript.Transcript.scalar aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32) := by rfl
'''
header='''import R1Z.PV_RunJoin_PrepareMaterialContext49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareScalarContext49
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
'''
out=header+'\n'+body+'\n\n'+source+'#print axioms source\nend R1Z.PV_RunJoin_PrepareScalarContext49\n'
p=L/'PV_RunJoin_PrepareScalarContext49.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(E/'scalar-context-source-identity.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),scalar_calls=count,tags=[27,28],other_calls_and_branches_unchanged=True),indent=2)+'\n')
