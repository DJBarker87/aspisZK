from pathlib import Path
import sys,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';p=2147483647;x=351017421
s='''import R1Z.PV_RunJoin_SquareChain20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InverseChain20
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort
'''
counter=0;proof=[]
def mul(a,b):
 global s,counter
 z=a*b%p;name=f'mul{counter}';counter+=1
 s+=f'''theorem {name} : aspis_core.field.M31.mul {a}#u32 {b}#u32 = ok {z}#u32 := by
  with_unfolding_all rfl
#print axioms {name}
'''
 return z,name
def square(a,n,k):
 global s
 vals=[a];names=[]
 for _ in range(n):
  z,name=mul(vals[-1],vals[-1]);vals.append(z);names.append(name)
 state=f'states{k}'
 s+=f'def {state} (n : Nat) : U32 := match n with\n'+''.join(f'  | {i} => {v}#u32\n' for i,v in enumerate(vals))+f'  | _ => {vals[-1]}#u32\n'
 s+=f'''theorem square{k} : aspis_core.field.square_n {a}#u32 {n}#usize = ok {vals[-1]}#u32 := by
  have hf : ∀ i, i < {n} → aspis_core.field.M31.mul ({state} i) ({state} i) = ok ({state} (i+1)) := by
    intro i hi
    interval_cases i
'''+''.join(f'    · exact {name}\n' for name in names)+f'  exact PV_RunJoin_SquareChain20.source {state} {n}#usize hf\n#print axioms square{k}\n'
 return vals[-1],f'square{k}'
a,n=mul(x,x);proof.append(n)
t2,n=mul(a,x);proof.append(n)
a,n=square(t2,2,2);proof.append(n)
t4,n=mul(a,t2);proof.append(n)
a,n=square(t4,4,4);proof.append(n)
t8,n=mul(a,t4);proof.append(n)
a,n=square(t8,8,8);proof.append(n)
t16,n=mul(a,t8);proof.append(n)
a,n=square(t16,8,16);proof.append(n)
t24,n=mul(a,t8);proof.append(n)
a,n=square(t24,4,24);proof.append(n)
t28,n=mul(a,t4);proof.append(n)
a,n=mul(t28,t28);proof.append(n)
t29,n=mul(a,x);proof.append(n)
t30,n=mul(t29,t29);proof.append(n)
a,n=mul(t30,t30);proof.append(n)
inv,n=mul(a,x);proof.append(n)
assert x*inv%p==1
s+=f'''theorem inverse : aspis_core.field.M31.inv {x}#u32 = ok {inv}#u32 := by
  rw [aspis_core.field.M31.inv]
  simp only [show (({x}#u32 : U32) != 0#u32) = true from rfl,massert,if_true,bind_tc_ok]
'''
for i,name in enumerate(proof):
 s+=f'  rw [{name}]\n'
 if i<len(proof)-1:s+='  simp only [bind_tc_ok]\n'
s+='#print axioms inverse\n'
s+=f'''theorem product : aspis_core.field.M31.mul {x}#u32 {inv}#u32 = ok 1#u32 := by
  with_unfolding_all rfl
#print axioms product
end R1Z.PV_RunJoin_InverseChain20
'''
q=L/'PV_RunJoin_InverseChain20.lean'
if '--check' in sys.argv:assert q.read_text()==s
else:q.write_text(s)
print(json.dumps(dict(input=x,inverse=inv,scalar_cells=counter,squaring_loops=5,large_power_reduction=False)))
