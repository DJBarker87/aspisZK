from pathlib import Path
import runpy,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
x=runpy.run_path(str(P/'JGo_arithmetic.py'))
for tag,scalar,n in [('0','JFq_Alpha0',4),('1','JFq_Alpha1',4),('K','JFq_Kappa',7)]:
 mod='JGo_TX2_Powers'+tag;alpha=x['scalar'](scalar);values=[[1]+[0]*7]
 for i in range(n-1):values.append(x['mul'](values[-1],alpha))
 s=f'''import JGo_TX2_LoopChain
import JGo_TX2_Range
import FIo_Install
import {scalar}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev State := Array E {n}#usize × E × Usize
def x : E := FIo_Install.toE {scalar}.scalar
'''
 for i,v in enumerate(values):
  s+=f'def p{i} : E := '+('FIo_Native.aspis_core.field.wide_exact.WideExact.ONE' if i==0 else x['wide'](v))+'\n'
 for i in range(n+1):
  s+=f'def a{i} : Array E {n}#usize := '+(f'Array.repeat {n}#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' if i==0 else f'Array.make {n}#usize ['+','.join(f'p{j}' if j<i else 'FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' for j in range(n))+']')+'\n'
 for i in range(n):
  rhs=f'.cont (a{i+1},p{i+1},{i+1}#usize)' if i<n-1 else f'.done a{n}'
  s+=f'''theorem step{i} : FIo_Native.weights.powers_loop.body x a{i} p{i} {i}#usize=ok ({rhs}) := by
  have inc : Usize.wrapping_add {i}#usize 1#usize={i+1}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value {i}#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : {i}#usize<{n}#usize)]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  with_unfolding_all rfl
#print axioms step{i}
'''
 s+='def states : Nat → State\n'
 for i in range(n-1):s+=f'  | {i} => (a{i},p{i},{i}#usize)\n'
 s+=f'  | _ => (a{n-1},p{n-1},{n-1}#usize)\n'
 s+=f'''theorem source : FIo_Native.weights.powers {n}#usize x=ok a{n} := by
  unfold FIo_Native.weights.powers FIo_Native.weights.powers_loop
  apply JGo_TX2_LoopChain.source
    (fun s : State=>match s with | (out,p,i)=>FIo_Native.weights.powers_loop.body x out p i)
    states {n-1} a{n}
  · intro i hi
    interval_cases i
'''
 for i in range(n-1):s+=f'    · exact step{i}\n'
 s+=f'  · exact step{n-1}\n#print axioms source\nend AspisR1.{mod}\nend\n'
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('three native pairing powers modules')
