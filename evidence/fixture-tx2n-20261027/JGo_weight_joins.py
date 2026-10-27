from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
mods={}
s='\n'.join(f'import JGo_TX2_WeightRow{k}' for k in range(5))+'''
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRows
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev Range := core.ops.range.Range Usize
'''
for k in range(5):
 point=k if k<3 else k-3;first=0 if k<3 else 1; nsteps=5-first
 typ='Range × Factors' if k<3 else 'Range × Factors × Q'
 s+=f'def states{k} : Nat → {typ}\n'
 for t in range(nsteps):
  d=t+first;n=k*5+d
  state=f'({{start:={d}#usize,«end»:=5#usize}},factors{n:02}'+(')' if k<3 else f',x{point}_{d})')
  s+=f'  | {t} => {state}\n'
 s+=f'  | _ => ({{start:=5#usize,«end»:=5#usize}},factors{(k+1)*5:02}'+(')\n' if k<3 else f',x{point}_5)\n')
 loop=f'weights_new_loop{0 if k<3 else 1}_loop0';body=loop+'.body'
 if k<3:
  call=f'{loop} {{start:=0#usize,«end»:=5#usize}} points factors{k*5:02} {k}#usize'
  b=f'fun s : {typ}=>{body} points {k}#usize s.1 s.2'
 else:
  call=f'{loop} {{start:=1#usize,«end»:=5#usize}} factors{k*5+1:02} {point}#usize x{point}_1'
  b=f'fun s : {typ}=>{body} {point}#usize s.1 s.2.1 s.2.2'
 s+=f'''theorem inner{k} : {call}=ok factors{(k+1)*5:02} := by
  unfold {loop}
  apply JGo_TX2_LoopChain.source ({b}) states{k} {nsteps} factors{(k+1)*5:02}
  · intro i hi
    interval_cases i
'''
 for t in range(nsteps):s+=f'    · exact JGo_TX2_WeightRow{k}.step{t+first}\n'
 s+='  · rfl\n'+f'#print axioms inner{k}\n'
s+='end AspisR1.JGo_TX2_WeightRows\nend\n'
mods['JGo_TX2_WeightRows.lean']=s
for f,s in mods.items():(R/'lean'/f).write_text(s)
