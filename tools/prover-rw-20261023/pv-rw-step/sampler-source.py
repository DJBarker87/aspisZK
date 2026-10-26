"""Promote literal emitted sampler leaf with the known shift-numeral API map."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026'
s=(e/'sampler-limb-Funs.lean.txt').read_text();a=s.index('/-- [aspis_core::field::P]');b=s.index('\nend PV_RW_SamplerNative',a);body=s[a:b]
assert body.count('32#i32')==1
body=body.replace('32#i32','32#u32')
out='''import R1Z.PV_OrdinaryDivBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_SamplerLimbSource
open Aeneas Aeneas.Std Result ControlFlow Error
'''+body+'''

def owned (limb : U32) (remainder : U64) : Result (U32 × U64) := do
  let dividend := U64.wrapping_shl remainder 32#u32 |||
    core.convert.num.FromU64U32.from limb
  let divisor := core.convert.num.FromU64U32.from PV_OrdinarySource.aspis_core.field.P
  let quotient ← dividend / divisor
  let next ← dividend % divisor
  ok (UScalar.cast .U32 quotient,next)

theorem limb (word : U32) (remainder : U64) :
    sampler_step.shipped_limb word remainder = owned word remainder := by
  simp only [sampler_step.shipped_limb,owned,aspis_core.field.P,
    PV_OrdinarySource.aspis_core.field.P,lift,bind_tc_ok]
#print axioms limb
end R1Z.PV_RW_SamplerLimbSource
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_SamplerLimbSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(e/'sampler-limb-emission-map.json').write_text(json.dumps(dict(emitted_sha256=hashlib.sha256(s.encode()).hexdigest(),lean_sha256=hashlib.sha256(out.encode()).hexdigest(),adaptations=['Import/namespace/boilerplate only','One wrapping_shl shift literal32#i32→32#u32, same pinned Aeneas scalar API adaptation as retained sampler; numerical shift32 unchanged. Native Kani checks the actual Rust signed default literal.'],new_axioms=0,scope='Machine operation order and complete Result comparison only, no whole callback installation.'),indent=2)+'\n')
