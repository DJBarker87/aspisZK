#!/usr/bin/env python3
"""Pin the three concrete source callee substitutions in the public prefix."""
from pathlib import Path
import hashlib,json,argparse
root=Path(__file__).resolve().parents[2]
p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterPrefix.lean'
s=p.read_text();d=s[s.index('def prepare '):s.index('\ndef caller\n')].rstrip()
r={'''  let context ←
    aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
      a a1''':'''  let context := ProverRwOuterContextModel.context a a1''',
'''  let i ← transport.Variant.tag variant''':'''  let i := ProverRwOuterTag.byte variant''',
'''  let a2 ←
    aspis_core.state_only_hiding.StateOnlyHidingContext.encode context''':'''  let a2 := ProverRwOuterEncode.value context'''}
for old,new in r.items():assert d.count(old)==1;d=d.replace(old,new)
d=d.replace('def prepare ','def direct ',1)
t='''import R1Z.ProverRwOuterTag
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterPrepare
open Aeneas Aeneas.Std Result ProverRwFull

'''+d+'''

variable [ExternalTypes]
/-- Exact actual public prefix with all three source leaves discharged. Both
hash calls, their ordered arguments, and their failure/divergence remain. -/
theorem prepare_direct (ops : ExternalFuns) (val : alloc.vec.Vec U8)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (nonce : Array U8 32#usize) :
    @ProverRwOuterPrefix.prepare _ (ProverRwOuterTag.selected ops) val v hash nonce =
      direct val v hash nonce := by
  unfold ProverRwOuterPrefix.prepare direct
  simp only [ProverRwOuterTag.construct_installed,ProverRwOuterTag.tag_installed,
    ProverRwOuterTag.encode_installed,bind_tc_ok]

#print axioms prepare_direct
end R1Z.ProverRwOuterPrepare
'''
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterPrepare.lean'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
if args.check:assert out.read_text()==t
else:out.write_text(t)
print(json.dumps({'source':str(p.relative_to(root)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(t.encode()).hexdigest(),'substitutions':list(r.items())}))
