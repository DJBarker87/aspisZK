"""Keep precise source slices for independent local operation checking.
Whole selected64 emission remains failed and is not replaced by these slices.
"""
from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
pre='import R1Z.ProverRwRngExtractor005Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnoncomputable section\n'
S='ProverRwRngExtractorsynthetic';N='ProverRwRngExtractorselected64'
def body(p,n):return p.read_text().split('namespace '+n+'\n',1)[1].rsplit('end '+n,1)[0]
t=body(D/'synthetic-generated005/Types.lean',S);f=body(D/'synthetic-generated005/Funs.lean',S)
t=t.replace('@[discriminant isize]\n','')
s=pre+'namespace '+S+'\n'+t+f+'end '+S+'\n'
raw=body(D/'selected64-generated005/Funs.lean',N)
# Exact complete emitted definitions: map_err, From and its instance; actual inner disposal closure and instance.
a=raw.index('/-- [core::result::');b=raw.index('/-- [aspis_prover::state_only_entropy::entropy_nonzero32')
c=raw.index('/-- [aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::closure::{impl core::ops::function::FnOnce<')
e=raw.index('/-- [aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::{impl core::ops::function::FnMut<',c)
s+='namespace '+N+'\n'+raw[a:b]+raw[c:e]+'end '+N+'\n'
p=L/'ProverRwRngExtractor005Local.lean';assert not p.exists();p.write_text(s)
(D/'local-slices005.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256((D/'selected64-generated005/Funs.lean').read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),selected_blocks=[raw[a:b],raw[c:e]],exclusions='generator, outer retry and borrowed FnMut callback excluded; full emission failure retained; no whole callback claim'),indent=2)+'\n')
