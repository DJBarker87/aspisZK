"""Named symbolic expansions: never evaluate a field operation or recurrence."""
from pathlib import Path
import sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean'
files={}
s='''import PV_B3P_IndexSteps9227
import PV_B3P_UsizeLoop9227
import PV_B3P_ReverseLoop9227
import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem result_right {α : Type} (r : Result α) : (r >>= Result.ok) = r := by
  cases r <;> rfl
#print axioms result_right
'''
for i in range(1,10):
 for kind,op,j in [('next','wrapping_add',i+1),('previous','wrapping_sub',i-1)]:
  s+=f'\ntheorem {kind}_{i} : Usize.{op} {i}#usize 1#usize = {j}#usize := {kind}_exact _ _ rfl\n#print axioms {kind}_{i}\n'
for kind,start in [('forward',1),('reverse',9)]:
 n=9;expr='do\n'
 for k in range(n):
  idx=start+k if kind=='forward' else start-k-1
  state='initial'if k==0 else f's{k-1}'
  expr+=f'    let s{k} ← step {state} {idx}#usize\n' if k<n-1 else f'    step {state} {idx}#usize'
 plan='usize_plan'if kind=='forward'else'reverse_plan'
 s+=f'''\ntheorem {kind}_nine (step : {{α : Type}} → α → Usize → Result α) := True.intro\n''' if False else f'''\ntheorem {kind}_nine {{α : Type}} (step : α → Usize → Result α) (initial : α) :
    {plan} step 9 {start}#usize initial = ({expr}) := by
  simp only [{plan},lift,bind_tc_ok,result_right,{','.join(f'next_{i}' if kind=='forward' else f'previous_{i}' for i in range(1,10))}]
#print axioms {kind}_nine
'''
s+='\nend PV_B3P_Binding9227\n'
files['PV_B3P_NineUnroll9227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print(json.dumps(dict(modules=list(files),field_operations_evaluated=False)))
