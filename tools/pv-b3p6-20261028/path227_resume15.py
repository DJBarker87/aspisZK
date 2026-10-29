from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(D/'raw227-composition-resume5/Funs.lean').read_text();files={}
decl=re.search(r'^def reference_terminal.path_lanes_literal\b[\s\S]*?(?=^/--|\Z)',raw,re.M)[0];lines=decl.split(':= do\n',1)[1].strip('\n').splitlines();ends=[i+1 for i,l in enumerate(lines)if re.match(r'  let path\d+ ← Array.update',l)];assert len(ends)==16
start=ends[0];pairends=ends[2::2];assert len(pairends)==7
h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
pars='(path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31)'
args='path_selector openings bit minus right';bounds='(hsub : aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit = .ok minus) (hmul : aspis_core.field.QM31.mul path_selector bit = .ok right)'
s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\nimport PV_B3P_Success227\n'+h+'''
abbrev PathState15 := Array aspis_core.field.QM31 17#usize
/-- Each source iteration repeats both the ONE-bit subtraction and the
path_selector*bit product. They are NOT silently cached in this interpreter. -/
def path_step15 (path_selector : aspis_core.field.QM31)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (bit : aspis_core.field.QM31) (state : PathState15) (lane : Usize) : Result PathState15 := do
  let source ← lift (Usize.wrapping_add 1#usize lane)
  let current ← Array.index_usize openings.z source
  let minus ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit
  let left ← aspis_core.field.QM31.mul path_selector minus
  let next ← Array.index_usize openings.succ_z lane
  let diff ← aspis_core.field.QM31.sub next current
  let weighted ← aspis_core.field.QM31.mul left diff
  let target ← lift (Usize.wrapping_add 1#usize lane)
  let state1 ← Array.update state target weighted
  let right ← aspis_core.field.QM31.mul path_selector bit
  let source1 ← lift (Usize.wrapping_add aspis_statement.poseidon2.RATE lane)
  let next1 ← Array.index_usize openings.succ_z source1
  let diff1 ← aspis_core.field.QM31.sub next1 current
  let weighted1 ← aspis_core.field.QM31.mul right diff1
  let base ← lift (Usize.wrapping_add 1#usize aspis_statement.poseidon2.DIGEST_ELEMS)
  let target1 ← lift (Usize.wrapping_add base lane)
  Array.update state1 target1 weighted1
end PV_B3P_Native15227
''';files['PV_B3P_PathStep15227']=s
for n in reversed(range(8)):
 mod=f'PV_B3P_PathCell15_{n}227';prev=f'PV_B3P_PathCell15_{n+1}227'if n<7 else 'PV_B3P_PathStep15227'
 incoming='path'+str(2*n+1);tail='\n'.join(lines[start if n==0 else pairends[n-1]:]);tail=re.sub(r'\b'+incoming+r'\b','state',tail);tail=re.sub(r'\bq3\b','minus',tail);tail=re.sub(r'\bq8\b','right',tail)
 nxt=f'path_tail15_{n+1} {args}'if n<7 else 'Result.ok'
 s='import '+prev+'\n'+h
 s+=f'\ndef path_tail15_{n} {pars} (state : PathState15) : Result PathState15 := do\n'+tail+'\n'
 s+='attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul path_step15'+(f' path_tail15_{n+1}'if n<7 else '')+'\n'
 s+=f'''theorem path_cell15_{n} {pars} (state : PathState15) {bounds} :
    path_tail15_{n} {args} state = (path_step15 path_selector openings bit state {n}#usize >>= {nxt}) := by
  unfold path_tail15_{n}
  conv_rhs => simp only [path_step15,PV_B3P_Ordered227.bind_assoc,lift,bind_tc_ok,hsub,hmul]
  simp only [lift,bind_tc_ok,hsub,hmul]
'''
 for j in range(10 if n<7 else 9):s+=f'  apply bind_equal9\n  intro v{j}\n'
 if n<7:s+=f'  unfold path_tail15_{n+1}\n  rfl\n'
 else:s+='  exact (PV_B3P_Binding9227.result_right _).symm\n'
 s+=f'''theorem path_fold15_{n} {pars} (state : PathState15) {bounds} :
    path_tail15_{n} {args} state =
      PV_B3P_Ordered227.fold (path_step15 path_selector openings bit)
        [{','.join(str(i)+'#usize'for i in range(n,8))}] state := by
  rw [path_cell15_{n} {args} state hsub hmul]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
'''
 if n<7:s+=f'''  apply congrArg (fun k => path_step15 path_selector openings bit state {n}#usize >>= k)
  funext next
  exact path_fold15_{n+1} {args} next hsub hmul
'''
 else:s+='  all_goals rfl\n'
 s+=f'#print axioms path_cell15_{n}\n#print axioms path_fold15_{n}\nend PV_B3P_Native15227\n';files[mod]=s
prefix='\n'.join(lines[:start]);s='import PV_B3P_PathCell15_0227\nimport PV_B3P_NativeLeading15227\n'+h
basic='(path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)'
s+=f'\ndef native_path15 {basic} : Result PathState15 := do\n'+prefix+'''
  range_loop13 (path_step15 path_selector openings bit) 0#usize 8#usize path1
'''
s+='attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul path_step15 path_tail15_0\n'
s+=f'''theorem native_path_binding15 {basic} :
    native_path15 path_selector openings = reference_terminal.path_lanes_literal path_selector openings := by
  unfold native_path15 reference_terminal.path_lanes_literal
'''
for j in range(sum('←'in l for l in lines[:start])):s+=f'  apply bind_equal9\n  intro p{j}\n'
s+='''  obtain ⟨minus,hsub⟩ := PV_B3P_Success227.qsub aspis_core.field.QM31.ONE p0
  obtain ⟨right,hmul⟩ := PV_B3P_Success227.qmul path_selector p0
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  simpa only [path_tail15_0] using (path_fold15_0 path_selector openings p0 minus right p4 hsub hmul).symm
#print axioms native_path_binding15
end PV_B3P_Native15227
''';files['PV_B3P_NativePath15227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume15/path-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
print(' '.join(files))
