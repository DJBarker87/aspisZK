"""Factor one exact emitted continuation per module, deepest first.
No arithmetic evaluation; each cell uses only named next-stage and one-step laws.
"""
from pathlib import Path
import re,json,hashlib
import sys
if '--check' in sys.argv:
 def checked_write(path, data, *args, **kwargs):
  assert path.read_text() == data, ('generator drift',str(path))
  return len(data)
 Path.write_text = checked_write
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(D/'resume14/frontier-raw/Funs.lean').read_text()
body=raw.split('  := do\n',1)[1].split('\nend PV_B3P_Missing14Frontier')[0];lines=body.splitlines()
header='''namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
abbrev FF14 := alloc.vec.Vec U8 → Slice U32 → Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × alloc.vec.Vec U8)
abbrev FV14 := Array (Array U32 8#usize) 20#usize
abbrev FS14 := (core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × alloc.vec.Vec U8
'''
base='import PV_B3P_Frontier14Port\n'+header+'''
def frontier_step14 (fields : FF14) (next : alloc.vec.Vec U8 → FV14 → Result FS14)
    (index : Usize) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do
  let row ← Array.index_usize values index
  let slice ← lift (Array.to_slice row)
  let (r,out1) ← fields out slice
  let branch ← core.result.Result.Insts.CoreOpsTry.branch r
  match branch with
  | .Continue _ => next out1 values
  | .Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual
    .ok (error,out1)
def suffix20_14 (_fields : FF14) (out : alloc.vec.Vec U8) (_values : FV14) : Result FS14 := .ok (.Ok (),out)
#print axioms suffix20_14
end PV_B3P_FrontierStages14227
'''
(L/'PV_B3P_FrontierBase14227.lean').write_text(base)
mods=['PV_B3P_FrontierBase14227']
for i in range(19,-1,-1):
 name='a' if i==0 else 'a'+str(i)
 start=next(j for j,l in enumerate(lines)if re.match(r'\s*let '+name+r' ←',l))
 indent=len(lines[start])-len(lines[start].lstrip())
 finish=next((j for j in range(start+1,len(lines))if lines[j].startswith(' '*(indent-2)+'| core.ops.control_flow.ControlFlow.Break')),len(lines)) if i else len(lines)
 chunk='\n'.join('  '+l[indent:] for l in lines[start:finish])
 if i:chunk=re.sub(r'\bout'+str(i)+r'\b','out',chunk)
 mod=f'PV_B3P_FrontierStage14_{i:02d}227';prev=mods[-1]
 s=f'import {prev}\nnamespace PV_B3P_FrontierStages14227\nopen Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result\nset_option autoImplicit false\n'
 s+=f'def suffix{i}_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do\n'+chunk+'\n'
 s+=f'''theorem factor{i}_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) :
    suffix{i}_14 fields out values = frontier_step14 fields (suffix{i+1}_14 fields) {i}#usize out values := by
  unfold suffix{i}_14 frontier_step14 suffix{i+1}_14
  rfl
#print axioms factor{i}_14
end PV_B3P_FrontierStages14227
'''
 (L/(mod+'.lean')).write_text(s);mods.append(mod)
(D/'resume14/frontier-stage-manifest.json').write_text(json.dumps(dict(modules=mods,raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),shape='20 exact emitted continuation suffixes; one one-step factorization per module'),indent=2)+'\n')
print(' '.join(mods))
