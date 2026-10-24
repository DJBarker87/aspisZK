from pathlib import Path
import re,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[2]
t=(D/'generated/Types.lean').read_text();f=(D/'generated/Funs.lean').read_text()
t=t[t.index('namespace ProverRwRngNative'):].replace('end ProverRwRngNative','').replace('@[discriminant isize]\n','')
f=f[f.index('/-- Trait implementation:'):]
# Source extraction cannot translate the Rust nonzero scalar validity pattern.
# Parameters are uninstalled types, never an axiom or a u8 association.
pre='''import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace ProverRwRngNative
class NativeTypes where
  inner : Type
  nonzero : Type → Type → Type
abbrev core.num.niche_types.NonZeroI32Inner [NativeTypes] := NativeTypes.inner
abbrev core.num.nonzero.NonZero [NativeTypes] := NativeTypes.nonzero
variable [NativeTypes]
end ProverRwRngNative
'''
t=t.replace('namespace ProverRwRngNative','namespace ProverRwRngNative\nvariable [NativeTypes]')
a=(D.parent/'rng-preflight/adapt.py').read_text();extern=a.split("extern='''",1)[1].split("'''",1)[0]
extern+='''
def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) : Result (core.result.Result T F) :=
  match status with
  | .Ok x => .ok (.Ok x)
  | .Err e => do
    let mapped ← inst.call_once closure e
    .ok (.Err mapped)
'''
out=pre+t+extern+f
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeEmission.lean';p.write_text(out)
(D/'adaptation.json').write_text(json.dumps(dict(raw={n:hashlib.sha256((D/'generated'/n).read_bytes()).hexdigest() for n in ['Types.lean','Funs.lean','TypesExternal_Template.lean','FunsExternal_Template.lean']},output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes=['strip generated resource overrides','remove discriminant annotations producing unqualified global names colliding with accepted cap16 module; no declaration/body change','NativeTypes parameters for unsupported core NonZero niche carrier; no native installation or layout claim','same explicit value-level Zeroizing installation and unused ErasureFns callbacks as prior certificate','transparent source-shaped Result.map_err implementation; complete emitted concrete callback/retry bodies retained'],native_type_installed=False),indent=2)+'\n')
