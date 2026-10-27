from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
# Reuse the retained, already preflighted field arithmetic without executing its generator.
s=(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0]
x={};exec(compile(s,'retained-arithmetic','exec'),dict(__file__=str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')),x)
# exec globals must be shared for helper functions.
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec(s,x)
out={}
for tag,scalar,n in [('0','JFq_Alpha0',4),('1','JFq_Alpha1',4),('K','JFq_Kappa',7)]:
 alpha=x['scalar'](scalar);values=[[1]+[0]*7]
 for i in range(n-1):values.append(x['mul'](values[-1],alpha))
 mod='JGq_Powers'+tag
 t=f'''import JGo_TX2_LoopChain
import JGo_TX2_Range
import FIo_Install
import {scalar}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev S := Array E {n}#usize × E × Usize
def x : E := FIo_Install.toE {scalar}.scalar
'''
 for i,v in enumerate(values):t+=f'def p{i} : E := '+('FIo_Native.aspis_core.field.wide_exact.WideExact.ONE' if i==0 else x['wide'](v))+'\n'
 for i in range(n+1):t+=f'def a{i} : Array E {n}#usize := '+(f'Array.repeat {n}#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' if i==0 else f'Array.make {n}#usize ['+','.join(f'p{j}' if j<i else 'FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' for j in range(n))+']')+'\n'
 out[mod+'Data']=t+f'end AspisR1.{mod}\nend\n'
 for i in range(n):
  m=mod+f'Step{i}';rhs=f'.cont (a{i+1},p{i+1},{i+1}#usize)' if i<n-1 else f'.done a{n}'
  t=f'''import {mod}Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result ControlFlow
'''
  if i<n-1:t+=f'''theorem multiply{i} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul p{i} x=ok p{i+1} := by with_unfolding_all rfl
#print axioms multiply{i}
'''
  t+=f'''theorem step{i} : FIo_Native.weights.powers_loop.body x a{i} p{i} {i}#usize=ok ({rhs}) := by
  have inc : Usize.wrapping_add {i}#usize 1#usize={i+1}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value {i}#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : {i}#usize<{n}#usize)]
  have idx : Array.index_mut_usize a{i} {i}#usize=ok (a{i}.val[{i}],fun v=>a{i+1}.set ⟨{i},by decide⟩ v) := by rfl
  rw [idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [{'if_neg (by scalar_tac : '+str(i+1)+'#usize≠'+str(n)+'#usize)' if i<n-1 else 'if_pos True.intro'}]
'''
  if i<n-1:t+=f'  rw [multiply{i},bind_tc_ok]\n'
  t+='  rfl\n'+f'#print axioms step{i}\nend AspisR1.{mod}\nend\n'
  # Array.set is not a known Aeneas API: use its actual list update back instead.
  t=t.replace(f'  have idx : Array.index_mut_usize a{i} {i}#usize=ok (a{i}.val[{i}],fun v=>a{i+1}.set ⟨{i},by decide⟩ v) := by rfl\n  rw [idx,bind_tc_ok]\n',f'  have idx : Array.index_usize a{i} {i}#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl\n  rw [Array.index_mut_usize,idx,bind_tc_ok]\n')
  out[m]=t
 t='\n'.join('import '+mod+f'Step{i}' for i in range(n))+f'''\nset_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result ControlFlow
def states : Nat → S
'''
 for i in range(n-1):t+=f'  | {i} => (a{i},p{i},{i}#usize)\n'
 t+=f'''  | _ => (a{n-1},p{n-1},{n-1}#usize)
theorem source : FIo_Native.weights.powers {n}#usize x=ok a{n} := by
  unfold FIo_Native.weights.powers FIo_Native.weights.powers_loop
  apply JGo_TX2_LoopChain.source
    (fun s : S=>match s with | (out,p,i)=>FIo_Native.weights.powers_loop.body x out p i)
    states {n-1} a{n}
  · intro i hi
    interval_cases i
'''
 for i in range(n-1):t+=f'    · exact step{i}\n'
 t+=f'  · exact step{n-1}\n#print axioms source\nend AspisR1.{mod}\nend\n';out[mod]=t
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'power stages checked' if '--check' in sys.argv else 'power stages generated')
