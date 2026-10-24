from pathlib import Path
import re,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[2]
t=(D/'generated/Types.lean.txt').read_text();f=(D/'generated/Funs.lean.txt').read_text();e=(D/'generated/FunsExternal_Template.lean.txt').read_text()
# Archive raw generated options unchanged; normalize the imported adaptation to defaults.
t=re.sub(r'/\- You can set the `max(?:Heartbeats|RecDepth)`[^\n]*\nset_option max(?:Heartbeats|RecDepth) \d+\n', '', t)
t=t.replace('end ProverRwRng','')
extern='''
-- Unused erasure callbacks stay explicit parameters. Their runtime/drop
-- semantics are not asserted by this value-level installation.
class ErasureFns where
  scalar : {Z : Type} → zeroize.DefaultIsZeroes Z → Z → Result Z
  array : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Array Z N → Result (Array Z N)
variable [ErasureFns]
def zeroize.Zeroize.Blanket.zeroize {Z : Type} (d : zeroize.DefaultIsZeroes Z) : Z → Result Z := ErasureFns.scalar d
def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Usize} (d : zeroize.Zeroize Z) : Array Z N → Result (Array Z N) := ErasureFns.array d
-- Value-level transparent new/deref installation, not a physical drop theorem.
def zeroize.Zeroizing.new {Z : Type} (_ : zeroize.Zeroize Z) (z : Z) : Result (zeroize.Zeroizing Z) := .ok z
def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result Z := .ok z
def zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result (Z × (Z → zeroize.Zeroizing Z)) := .ok (z,id)
'''
f=f[f.index('/-- Trait implementation:'):]
out=t+extern+f
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngEmission.lean';p.write_text(out)
pin=lambda x:hashlib.sha256(x.encode()).hexdigest()
# Bind by rust qualified names + complete declaration signatures, never op number.
entries=[]
for m in re.finditer(r'/-- \[([^\n]+)[\s\S]*?\naxiom ([\s\S]*?)(?=\n/--|\Z)',e):
 entries.append(dict(qualified_source=m.group(1),template_signature=m.group(2).strip(),template_signature_sha256=pin(m.group(2).strip())))
(D/'adaptation.json').write_text(json.dumps({'inputs':{n:pin((D/'generated'/n).read_text()) for n in ['Types.lean.txt','Funs.lean.txt','FunsExternal_Template.lean.txt']},'output':str(p.relative_to(R)),'output_sha256':pin(out),'external_bindings':entries,'changes':['remove generated maxHeartbeats/maxRecDepth overrides; default options; raw input archives unchanged','combine type/fun modules without rewriting emitted control','two unused erasure callbacks parameterized as ErasureFns','transparent value-level new/deref/deref_mut definitions; no native drop claim'],'no_implicit_world':True},indent=2)+'\n')
