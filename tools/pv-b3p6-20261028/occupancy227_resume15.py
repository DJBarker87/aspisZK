"""Factor all eight occupancy writes, then reconstruct the actual source range.
No arithmetic dictionary or large concrete term is evaluated.
"""
from pathlib import Path
import re,json,sys,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
decl=re.search(r'^def reference_terminal.occupancy_lanes_literal\b[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
lines=decl.split(':= do\n',1)[1].strip('\n').splitlines()
ends=[i+1 for i,l in enumerate(lines) if re.match(r'  let occupancy\d* ← Array.update',l)]
assert len(ends)==11
start=ends[2];ends=ends[3:]
head='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
pars='(input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) (occupied inverse one_minus both : aspis_core.field.QM31)'
args='input_occupancy output_occupancy expected_output opened occupied inverse one_minus both'
base='PV_B3P_OccupancyStep15227'
s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\n'+head+'''
abbrev OccupancyState15 := Array aspis_core.field.QM31 12#usize
def occupancy_step15 (opened : Array aspis_core.field.QM31 16#usize)
    (one_minus both : aspis_core.field.QM31) (state : OccupancyState15) (lane : Usize) : Result OccupancyState15 := do
  let source ← lift (Usize.wrapping_add 2#usize lane)
  let q ← Array.index_usize opened source
  let q1 ← aspis_core.field.QM31.mul one_minus q
  let q2 ← aspis_core.field.QM31.mul both q1
  let target ← lift (Usize.wrapping_add 3#usize lane)
  Array.update state target q2
'''
suffix='\n'.join(lines[ends[-1]:]);suffix=re.sub(r'\boccupancy11\b','state',suffix)
s+=f'\ndef occupancy_finish15 {pars} (state : OccupancyState15) : Result OccupancyState15 := do\n'+suffix+'\nend PV_B3P_Native15227\n';files[base]=s
for n in reversed(range(8)):
 mod=f'PV_B3P_OccupancyCell15_{n}227';prev=f'PV_B3P_OccupancyCell15_{n+1}227' if n<7 else base
 incoming='occupancy'+str(n+3);tail='\n'.join(lines[start if n==0 else ends[n-1]:]);tail=re.sub(r'\b'+incoming+r'\b','state',tail)
 nxt=f'occupancy_tail15_{n+1} {args}' if n<7 else 'occupancy_finish15 '+args
 s='import '+prev+'\n'+head
 s+=f'\ndef occupancy_tail15_{n} {pars} (state : OccupancyState15) : Result OccupancyState15 := do\n'+tail+'\n'
 s+='attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul aspis_core.field.QM31.add aspis_core.field.QM31.sub reference_terminal.lift_m31 occupancy_step15 occupancy_finish15'+(f' occupancy_tail15_{n+1}'if n<7 else '')+'\n'
 s+=f'''theorem occupancy_cell15_{n} {pars} (state : OccupancyState15) :
    occupancy_tail15_{n} {args} state =
      (occupancy_step15 opened one_minus both state {n}#usize >>= {nxt}) := by
  unfold occupancy_tail15_{n}
  conv_rhs => simp only [occupancy_step15,PV_B3P_Ordered227.bind_assoc,lift,bind_tc_ok]
  simp only [lift,bind_tc_ok]
'''
 for j in range(4):s+=f'  apply bind_equal9\n  intro v{j}\n'
 s+='  unfold '+(f'occupancy_tail15_{n+1}'if n<7 else 'occupancy_finish15')+'\n  rfl\n'
 s+=f'''theorem occupancy_fold15_{n} {pars} (state : OccupancyState15) :
    occupancy_tail15_{n} {args} state =
      (PV_B3P_Ordered227.fold (occupancy_step15 opened one_minus both)
        [{','.join(str(i)+'#usize'for i in range(n,8))}] state >>= occupancy_finish15 {args}) := by
  rw [occupancy_cell15_{n}]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
'''
 if n<7:s+=f'''  apply congrArg (fun k => occupancy_step15 opened one_minus both state {n}#usize >>= k)
  funext next
  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using occupancy_fold15_{n+1} {args} next
'''
 else:s+='  rfl\n'
 s+=f'#print axioms occupancy_cell15_{n}\n#print axioms occupancy_fold15_{n}\nend PV_B3P_Native15227\n';files[mod]=s
# Keep the entire source entry prefix, and replace only its eight-iteration range.
prefix='\n'.join(lines[:start]);nativeprefix=prefix
s='import PV_B3P_OccupancyCell15_0227\nimport PV_B3P_NativeLeading15227\n'+head
basic='(input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize)'
s+=f'\ndef native_occupancy15 {basic} : Result OccupancyState15 := do\n'+prefix+f'''
  let state ← range_loop13 (occupancy_step15 opened one_minus both) 0#usize 8#usize occupancy3
  occupancy_finish15 {args} state
'''
s+='attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul aspis_core.field.QM31.sub aspis_core.field.QM31.add reference_terminal.lift_m31 occupancy_tail15_0 occupancy_finish15 occupancy_step15\n'
s+=f'''theorem native_occupancy_binding15 {basic} :
    native_occupancy15 input_occupancy output_occupancy expected_output opened =
      reference_terminal.occupancy_lanes_literal input_occupancy output_occupancy expected_output opened := by
  unfold native_occupancy15 reference_terminal.occupancy_lanes_literal
'''
# There are 16 monadic prefix binds; count continuation lines, ignoring pure let.
binds=sum('←'in l for l in lines[:start])
for j in range(binds):s+=f'  apply bind_equal9\n  intro p{j}\n'
s+='  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]\n  simpa only [occupancy_tail15_0] using (occupancy_fold15_0 input_occupancy output_occupancy expected_output opened p0 p1 p2 p3 p15).symm\n'
s+='#print axioms native_occupancy_binding15\nend PV_B3P_Native15227\n';files['PV_B3P_NativeOccupancy15227']=s
for m,s in files.items():
 s=s.replace('reference_terminal.occupancy_lanes_literal','PV_B3P_227.reference_terminal.occupancy_lanes_literal')
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume15/occupancy-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
print(' '.join(files))
