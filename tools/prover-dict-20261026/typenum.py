"""Generate the terminal typenum interpretations; no UInt representation chosen."""
from pathlib import Path
import sys
r=Path(__file__).resolve().parents[2]
ops={}
ks=['isize','i64','i32','i16','i8','usize','u64','u32','u16','u8']
for i,k in enumerate(ks):ops[163+i]=f'.ok 0#{k}';ops[173+i]=f'.ok 0#{k}'
ops.update({183:'.ok ()',184:'fun x => .ok x',188:'.ok true',189:'.ok 1#u8',190:'.ok ()',191:'.ok true',192:'.ok 1#u8',193:'.ok ()',194:'fun x => .ok x',196:'.ok Ordering.eq',197:'.ok Ordering.gt',198:'.ok false',199:'.ok 0#u8',200:'.ok ()',201:'.ok false',202:'.ok 0#u8',203:'.ok ()',204:'fun x => .ok x'})
s='''import R1Z.PDict_WireError
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Typenum
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- These entries occur outside the successful proof-body cone. Native source
-- constants and ZST identities are checked in the cfg(kani) contract.
-- No UInt, GenericArray, SHA state, filesystem or effect type is instantiated.
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_WireError.selected ops with
'''
s+=',\n'.join(f'    op{i} := {v}' for i,v in sorted(ops.items()))+' }\n\n'
for i,v in sorted(ops.items()):
 if i in [184,194,204]:
  typ={184:'typenum.uint.UTerm',194:'typenum.bit.B1',204:'typenum.bit.B0'}[i]
  s+=f'theorem op{i}_installed (ops : ExternalFuns) (x : {typ}) :\n    (selected ops).op{i} x = .ok x := rfl\n\n'
 else:s+=f'theorem op{i}_installed (ops : ExternalFuns) :\n    (selected ops).op{i} = {v} := rfl\n\n'
for i in sorted(ops):s+=f'#print axioms op{i}_installed\n'
s+='end R1Z.PDict_Typenum\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_Typenum.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print(len(ops))
