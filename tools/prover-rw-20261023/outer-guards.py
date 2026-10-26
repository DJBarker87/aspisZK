#!/usr/bin/env python3
"""Pin the emitted after-layout continuation; no body operation is replaced."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2]
p=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=p.read_text();name='aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1'
a=s.index('def\n  '+name);b=s.index('\n/--',a);body=s[a:b].rstrip();header=body[:body.index('  := do')]
start=body.index('        let (b1, nonce_store1) ←')
header=header.replace('def\n  '+name,'def afterChecks',1)
tail='\n'.join(line[6:] if line.startswith('      ') else line for line in body[start:].splitlines())
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterAfterChecks.lean'
t='''import R1Z.ProverRwOuterCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterAfterChecks
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

'''+header+'  := do\n'+tail+'\n\nend R1Z.ProverRwOuterAfterChecks\n'
if '--check' in sys.argv:assert out.read_text()==t
else:out.write_text(t)
print(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(body.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),removed='three layout guards only; continuation unchanged')))
