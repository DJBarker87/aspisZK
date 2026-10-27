from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';data={}
for filename in ['FixtureHashData','PathData16','OutputData16']:
 for m in re.finditer(r'def s_(\d+)_(\d+) .*? := !\[(.*?)\]',(L/f'PV_RunJoin_{filename}.lean').read_text()):data[int(m[1]),int(m[2])]=list(map(int,m[3].split(',')))
meta=[]
for start in range(0,81,9):
 imports=['import R1Z.PV_RunJoin_BankCertificate19'];bodies=[]
 for j in range(start,start+9):
  group=1+3*((j-1)//3) if j else None
  imports.append(f'import R1Z.PV_RunJoin_ValidatorGroup{group:02}19' if j else 'import R1Z.PV_RunJoin_ValidatorCell0019')
  model=f'PV_RunJoin_ValidatorCell{j:02}19';name=f'PV_RunJoin_BankCell{j:02}19'
  initial=data[j,0]
  chained=j in [2,3,5,31,32,34,35,37,38]
  pre=data[j-1,23] if chained else [0]*8+initial[8:]
  assert pre[8:]==initial[8:]
  ab=[(initial[i]-pre[i])%2147483647 for i in range(8)]+[0]*8
  s=f'''set_option autoImplicit false
namespace R1Z.{name}
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
'''
  s+='def absorption : State := Array.make 16#usize ['+','.join(f'{v}#u32' for v in ab)+']\n'
  a=pre.copy()
  for k in range(9):
   s+=f'def a{k} : State := Array.make 16#usize ['+','.join(f'{v}#u32' for v in a)+']\n'
   if k<8:a[k]=(a[k]+ab[k])%2147483647
  assert a==initial
  s+='def absorbed (n : Nat) : State := match n with\n'+''.join(f'  | {k} => a{k}\n' for k in range(9))+'  | _ => a8\n'
  s+='def states (n : Nat) : State := match n with\n'+f'  | 0 => {model}.s0\n'+''.join(f'  | {n} => {model}.s{2*n+1}\n' for n in range(1,12))+f'  | _ => {model}.s0\n'
  s+='''theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
'''
  s+=''.join(f'  · exact ⟨{initial[k]}#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩\n' for k in range(8))
  s+='''#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
'''
  s+=''.join(f'  · exact ⟨{model}.s{2*n+2},{model}.pair{n}⟩\n' for n in range(11))
  s+=f'''#print axioms pairs
def certificate : Certificate := {{
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }}
end R1Z.{name}
'''
  bodies.append(s);meta.append(dict(cell=j,pre_kind='previous odd-round output' if chained else 'zero rate lanes; fixture capacity lanes',absorption='eight modular differences; high lanes zero',permutation=model,source_constructor_equation=False))
 s='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies);p=L/f'PV_RunJoin_BankCells{start:02}19.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
if '--check' not in sys.argv:(R/'evidence/pv-runjoin19-20261027/bank-cell-layout-plan.json').write_text(json.dumps(meta,indent=2)+'\n')
print('nine groups: each absorption certificate checks eight scalar adds and eight array writes')
