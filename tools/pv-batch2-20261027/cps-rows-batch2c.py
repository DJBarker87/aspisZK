from pathlib import Path
import sys,re
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');outs={}
for i in range(5):
 s=(L/f'PV_B2_C_ConstructorRow{i}.lean').read_text();body=s.split(' : Result Factors := do\n',1)[1].split(f'\ntheorem row{i}_total',1)[0];assert '  ok (' in body
 a=body.rindex('  ok (');body=body[:a]+'  k ('+body[a+len('  ok ('):]
 arg='points : Points' if i<3 else 'z : Array Point 2#usize';v='points' if i<3 else 'z'
 p=L/f'PV_B2_C_Row{i}Cps.lean'
 prev='PV_B2_C_ConstructorRow4' if i==0 else f'PV_B2_C_Row{i-1}Cps'
 steps=[f'  unfold row{i}']
 commands=list(re.finditer(r'^  let (.*?) (←|:=)',body,re.M))
 original=body[:body.rindex('  k (')]+'  ok ('+body[body.rindex('  k (')+len('  k ('):]
 for j,m in enumerate(commands):
  n=m[1]
  if m[2]==':=':
   end=commands[j+1].start() if j+1<len(commands) else len(body)
   pure=body[m.start():end].strip()
   steps.append('  '+pure)
   continue
  steps.append('  change ((do\n'+original[m.start():]+') >>= k) = (do\n'+body[m.start():]+')')
  steps.append('  rw [bind_assoc_eq]')
  steps.append('  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr')
  steps.append(('  rintro ⟨'+n[1:-1]+'⟩ _') if n.startswith('(') else '  intro '+('unused' if n=='_' else n)+' _')
 steps.append('  exact bind_tc_ok _ _')
 proof='\n'.join(steps)
 s=f'''import R1Z.{prev}
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row {i}: reassociation with an arbitrary Result continuation only. -/
theorem row{i}_cps {{α : Type}} (factors : Factors) ({arg})
    (k : Factors → Result α) :
    (row{i} factors {v} >>= k) = (do
'''+body+f''') := by
{proof}
#print axioms row{i}_cps
end PV_B2_C_ConstructorRows
'''
 outs[p]=s
for p,s in outs.items():
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
