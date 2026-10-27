from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
for k in range(14):
 mod=f'JGn_CopyPattern{k:02}'
 s=f'''import JGn_CopyPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def start : Result (Usize × field.QM31) :=
  pattern_values_literal_loop1_loop0 JGl_NumericData.a JGn_CopyPowers.powers
    0#usize pattern{k:02} field.QM31.ZERO
'''
 for n in range(1,17):
  prev='start' if n==1 else f't{n-1:02}'
  s+=f'''def t{n:02} : Result (Usize × field.QM31) := by jgn_tail {n} {prev}
theorem step{n:02} : {prev}=t{n:02} := by jgn_prefix {n}
#print axioms step{n:02}
'''
 s+='''def returned : Usize × field.QM31 := by jgn_return t16
def value : field.QM31 := returned.2

theorem source : start=ok (16#usize,value) := by
'''
 s+='  calc\n'
 for n in range(1,17):s+=f'    {"start" if n==1 else "_"}=t{n:02} := step{n:02}\n'
 s+='    _=ok (16#usize,value) := by jgn_eval\n#print axioms source\nend AspisR1.'+mod+'\nend\n'
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print('pattern prefixes validated' if '--check' in sys.argv else 'patterns generated with one-cell original-source prefixes; all exceptional zero-kind cells keep the exact source branch')
