"""Literal retained standard Option bodies; only namespace is rebound."""
from pathlib import Path
import hashlib,json,re,sys
r=Path(__file__).resolve().parents[3];p=r/'docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean';s=p.read_text()
names=['core.option.Option.ok_or','core.option.Option.Insts.CoreOpsTry_traitTry.branch','core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual'];blocks=[]
for name in names:
 m=re.search(r'\bdef\s+'+re.escape(name)+r'\b',s);assert m
 blocks.append(s[m.start():s.index('\n/--',m.end())].strip())
b='''import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryOptionSource
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := fun x => match x with | none => 0#isize | some _ => 1#isize

'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwDictionaryOptionSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryOptionSource.lean'
if '--check' in sys.argv:assert o.read_text()==b
else:
 o.write_text(b)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/option-source.json').write_text(json.dumps(dict(input=str(p.relative_to(r)),input_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=dict(zip(names,[hashlib.sha256(x.encode()).hexdigest() for x in blocks])),output_sha256=hashlib.sha256(b.encode()).hexdigest(),scope='Literal core option bodies; exact branch/residual constructors. Native ABI association remains separate.'),indent=2)+'\n')
