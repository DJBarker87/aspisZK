from pathlib import Path
import json
import sys
if '--check' in sys.argv:
 def checked_write(path, data, *args, **kwargs):
  assert path.read_text() == data, ('generator drift',str(path))
  return len(data)
 Path.write_text = checked_write
D=Path('evidence/pv-b3p6-20261028');L=D/'lean'
s='''import PV_B3P_FrontierStage14_00227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
def indexed14 (fields : FF14) : List Usize → alloc.vec.Vec U8 → FV14 → Result FS14
  | [],out,_ => .ok (.Ok (),out)
  | index::rest,out,values => frontier_step14 fields (fun out values => indexed14 fields rest out values) index out values

theorem suffix20_binding14 (fields : FF14) : suffix20_14 fields = indexed14 fields [] := rfl

theorem raw_frontier_binding14 (fields : FF14) : frontier fields = suffix0_14 fields := by
  funext out values
  unfold frontier suffix0_14
  rfl
#print axioms suffix20_binding14
#print axioms raw_frontier_binding14
#print alloc.vec.Vec
end PV_B3P_FrontierStages14227
'''
(L/'PV_B3P_FrontierIndexedBase14227.lean').write_text(s);mods=['PV_B3P_FrontierIndexedBase14227']
for i in range(19,-1,-1):
 mod=f'PV_B3P_FrontierCompose14_{i:02d}227'
 nums=lambda j:'['+', '.join(str(n)+'#usize'for n in range(j,20))+']'
 s=f'''import {mods[-1]}
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix{i}_binding14 (fields : FF14) :
    suffix{i}_14 fields = indexed14 fields {nums(i)} := by
  funext out values
  rw [factor{i}_14]
  rw [suffix{i+1}_binding14]
  rfl
#print axioms suffix{i}_binding14
end PV_B3P_FrontierStages14227
'''
 (L/(mod+'.lean')).write_text(s);mods.append(mod)
s=f'''import {mods[-1]}
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier
set_option autoImplicit false
/-- Exact extracted caller, preserving every Result and partial Err output,
composed through twenty named stage laws. No fields or Vec law is assumed. -/
theorem frontier_indexed_binding14 (fields : FF14) :
    frontier fields = indexed14 fields {nums(0)} :=
  Eq.trans (raw_frontier_binding14 fields) (suffix0_binding14 fields)
#print axioms frontier_indexed_binding14
end PV_B3P_FrontierStages14227
'''
mod='PV_B3P_FrontierIndexedBinding14227';(L/(mod+'.lean')).write_text(s);mods.append(mod)
(D/'resume14/frontier-compose-manifest.json').write_text(json.dumps(dict(modules=mods),indent=2)+'\n')
print(' '.join(mods))
