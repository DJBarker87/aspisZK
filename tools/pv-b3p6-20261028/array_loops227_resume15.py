"""Generate source loop/unroll associations one cell per focused module.
All callees stay opaque; the generator never emits arithmetic normalization.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(D/'raw227-composition-resume5/Funs.lean').read_text();files={}
h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
specs=[('Interpolation','reference_poseidon.interpolate_three_constant_columns',
 '(weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize)',
 'weights column0 column1 column2',
 '''  let c0 ← Array.index_usize column0 lane
  let c1 ← Array.index_usize column1 lane
  let c2 ← Array.index_usize column2 lane
  let value ← reference_poseidon.interpolate_column227 weights c0 c1 c2
  Array.update state lane value''',4),
 ('Absorption','reference_terminal.absorption_lanes_literal',
 '(low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize)',
 'low fixed chunk_two chunk_eight nodes openings',
 '''  let opened ← reference_terminal.read227 openings lane
  let value ← reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened
  Array.update state lane value''',2)]
for label,target,pars,args,stepbody,binds in specs:
 lo=label.lower();decl=re.search(r'^def '+re.escape(target)+r'\b[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
 lines=decl.split(':= do\n',1)[1].strip('\n').splitlines();assert lines[0].startswith('  let output := Array.repeat')
 ends=[i+1 for i,l in enumerate(lines)if re.match(r'  let output\d+ ← Array.update',l)];assert len(ends)==15
 base=f'PV_B3P_{label}Step15227'
 s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\n'+h
 s+=f'''\ndef {lo}_step15 {pars} (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
{stepbody}
end PV_B3P_Native15227
''';files[base]=s
 for n in reversed(range(16)):
  mod=f'PV_B3P_{label}Cell15_{n:02}227';prev=f'PV_B3P_{label}Cell15_{n+1:02}227'if n<15 else base
  incoming='output'if n==0 else 'output'+str(n)
  tail='\n'.join(lines[1 if n==0 else ends[n-1]:]);tail=re.sub(r'\b'+incoming+r'\b','state',tail)
  nxt=f'{lo}_tail15_{n+1:02} {args}'if n<15 else 'Result.ok'
  s='import '+prev+'\n'+h
  s+=f'\ndef {lo}_tail15_{n:02} {pars} (state : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) := do\n'+tail+'\n'
  s+='attribute [local irreducible] Array.index_usize Array.update reference_terminal.read227 reference_terminal.absorption_lane227 reference_poseidon.interpolate_column227 '+lo+'_step15'+(f' {lo}_tail15_{n+1:02}'if n<15 else '')+'\n'
  s+=f'''theorem {lo}_cell15_{n:02} {pars} (state : Array aspis_core.field.QM31 16#usize) :
    {lo}_tail15_{n:02} {args} state =
      ({lo}_step15 {args} state {n}#usize >>= {nxt}) := by
  unfold {lo}_tail15_{n:02}
  conv_rhs => simp only [{lo}_step15,PV_B3P_Ordered227.bind_assoc]
'''
  for j in range(binds):s+=f'  apply bind_equal9\n  intro v{j}\n'
  if n<15:s+=f'  apply bind_equal9\n  intro next\n  unfold {lo}_tail15_{n+1:02}\n  rfl\n'
  else:s+='  exact (PV_B3P_Binding9227.result_right _).symm\n'
  s+=f'''theorem {lo}_fold15_{n:02} {pars} (state : Array aspis_core.field.QM31 16#usize) :
    {lo}_tail15_{n:02} {args} state =
      PV_B3P_Ordered227.fold ({lo}_step15 {args}) [{','.join(str(i)+'#usize'for i in range(n,16))}] state := by
  rw [{lo}_cell15_{n:02}]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
'''
  if n<15:s+=f'''  apply congrArg (fun k => {lo}_step15 {args} state {n}#usize >>= k)
  funext next
  exact {lo}_fold15_{n+1:02} {args} next
'''
  else:s+='  all_goals rfl\n'
  s+=f'#print axioms {lo}_cell15_{n:02}\n#print axioms {lo}_fold15_{n:02}\nend PV_B3P_Native15227\n';files[mod]=s
 s=f'import PV_B3P_{label}Cell15_00227\n'+h
 s+=f'''\ndef native_{lo}15 {pars} : Result (Array aspis_core.field.QM31 16#usize) :=
  range_loop13 ({lo}_step15 {args}) 0#usize 16#usize
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO)

theorem native_{lo}_binding15 {pars} :
    native_{lo}15 {args} = {target} {args} := by
  unfold native_{lo}15
  rw [range_sixteen13]
  exact ({lo}_fold15_00 {args} _).symm
#print axioms native_{lo}_binding15
end PV_B3P_Native15227
''';files[f'PV_B3P_Native{label}15227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume15/array-loop-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
print(' '.join(files))
