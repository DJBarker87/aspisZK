"""Named one-lane cells for the internal Poseidon summation and write loops.
All arithmetic, extension conversion and array primitives remain locally opaque.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
decl=re.search(r'^def reference_poseidon.internal_linear_lazy\s*\n[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
lines=decl.split(':= do\n',1)[1].strip('\n').splitlines()
sum_starts=[i for i,l in enumerate(lines) if re.match(r'  let q\d+ ← Array.index_usize state \d+#usize',l)]
assert len(sum_starts)==15
sum_end=next(i for i,l in enumerate(lines) if 'let full_sum ←'in l)
out_starts=[i for i,l in enumerate(lines) if re.match(r'  let q\d+ ← Array.index_usize state\d+ \d+#usize',l)]
assert len(out_starts)==15
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result\nset_option autoImplicit false\n'
opaque='Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.internal_shift227 reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.extension_limbs'
base='PV_B3P_InternalSteps12227'
s='import PV_B3P_P227_06\nimport PV_B3P_DigestCpsEq9227\nimport PV_B3P_BindBranch12227\n'+h+'''
abbrev InternalState12 := Array aspis_core.field.QM31 16#usize
abbrev InternalSum12 := Array U64 4#usize
def internal_sum_step12 (state : InternalState12) (sum : InternalSum12) (lane : Usize) : Result InternalSum12 := do
  let value ← Array.index_usize state lane
  reference_poseidon.internal_sum227 sum value
def internal_output_step12 (full_sum : InternalSum12) (state : InternalState12) (lane : Usize) : Result InternalState12 := do
  let value ← Array.index_usize state lane
  let offset ← lift (Usize.wrapping_sub lane 1#usize)
  let shift ← Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS offset
  let output ← reference_poseidon.internal_shift227 value full_sum shift
  Array.update state lane output
end PV_B3P_Binding12227
''';files[base]=s
# Descending dependency order: one actual source lane per module.
for n in reversed(range(1,16)):
    mod=f'PV_B3P_InternalOutput12{n:02}227';prev=f'PV_B3P_InternalOutput12{n+1:02}227' if n<15 else base
    incoming='state'+str(n)
    tail='\n'.join(lines[out_starts[n-1]:]);tail=re.sub(r'\b'+incoming+r'\b','state',tail)
    params='(full_sum : InternalSum12) (state : InternalState12)'
    nxt=f'internal_output_tail12_{n+1:02} full_sum' if n<15 else 'Result.ok'
    s=f'import {prev}\nimport PV_B3P_IndexSteps9227\n'+h+f'def internal_output_tail12_{n:02} {params} : Result InternalState12 := do\n'+tail+'\n'
    s+='attribute [local irreducible] '+opaque+' internal_output_step12'+(f' internal_output_tail12_{n+1:02}'if n<15 else'')+'\n'
    s+=f'''theorem internal_output_cell12_{n:02} {params} :
    internal_output_tail12_{n:02} full_sum state =
      (internal_output_step12 full_sum state {n}#usize >>= {nxt}) := by
  have hsub : Usize.wrapping_sub {n}#usize 1#usize = {n-1}#usize := previous_exact _ _ rfl
  unfold internal_output_tail12_{n:02}
  conv_rhs => simp only [internal_output_step12,hsub,lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc,bind_return12]
'''
    if n<15:
        for j in range(3):s+=f'  apply bind_equal9\n  intro x{j}\n'
        s+=f'  apply bind_equal9\n  intro next\n  unfold internal_output_tail12_{n+1:02}\n  rfl\n'
    idx=', '.join(f'{i}#usize' for i in range(n,16))
    s+=f'''theorem internal_output_fold12_{n:02} {params} :
    internal_output_tail12_{n:02} full_sum state =
      PV_B3P_Ordered227.fold (internal_output_step12 full_sum) [{idx}] state := by
  rw [internal_output_cell12_{n:02}]
  simp only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12]
'''
    if n<15:
      s+=f'  apply congrArg (fun finish => internal_output_step12 full_sum state {n}#usize >>= finish)\n  funext next\n  simpa only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12] using internal_output_fold12_{n+1:02} full_sum next\n'
    s+=f'#print axioms internal_output_cell12_{n:02}\n#print axioms internal_output_fold12_{n:02}\nend PV_B3P_Binding12227\n';files[mod]=s
# Preserve the full-sum and lane-zero stores before the remaining fifteen writes.
s='import PV_B3P_InternalOutput1201227\n'+h
prefix='\n'.join(lines[sum_end:out_starts[0]])
prefix=re.sub(r'\bpart_sum15\b','part_sum',prefix)
s+='def internal_finish12 (state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12) : Result InternalState12 := do\n'+prefix+'\n  internal_output_tail12_01 full_sum state1\nend PV_B3P_Binding12227\n'
files['PV_B3P_InternalFinish12227']=s
for n in reversed(range(1,16)):
    mod=f'PV_B3P_InternalSum12{n:02}227';prev=f'PV_B3P_InternalSum12{n+1:02}227'if n<15 else 'PV_B3P_InternalFinish12227'
    incoming='part_sum'+(str(n-1)if n>1 else'')
    tail='\n'.join(lines[sum_starts[n-1]:]);tail=re.sub(r'\b'+incoming+r'\b','part_sum',tail)
    params='(state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12)'
    nxt=f'internal_sum_tail12_{n+1:02} state old_zero'if n<15 else'internal_finish12 state old_zero'
    s=f'import {prev}\nimport PV_B3P_IndexSteps9227\n'+h+f'def internal_sum_tail12_{n:02} {params} : Result InternalState12 := do\n'+tail+'\n'
    s+='attribute [local irreducible] '+opaque+' internal_sum_step12 internal_finish12'+(f' internal_sum_tail12_{n+1:02}'if n<15 else'')+'\n'
    s+=f'''theorem internal_sum_cell12_{n:02} {params} :
    internal_sum_tail12_{n:02} state old_zero part_sum =
      (internal_sum_step12 state part_sum {n}#usize >>= {nxt}) := by
  unfold internal_sum_tail12_{n:02}
  conv_rhs => simp only [internal_sum_step12,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro value
  apply bind_equal9
  intro next
'''
    if n<15:s+=f'  unfold internal_sum_tail12_{n+1:02}\n'
    else:s+='  unfold internal_finish12 internal_output_tail12_01\n'
    s+='  rfl\n'
    idx=', '.join(f'{i}#usize' for i in range(n,16))
    s+=f'''theorem internal_sum_fold12_{n:02} {params} :
    internal_sum_tail12_{n:02} state old_zero part_sum =
      (PV_B3P_Ordered227.fold (internal_sum_step12 state) [{idx}] part_sum >>= internal_finish12 state old_zero) := by
  rw [internal_sum_cell12_{n:02}]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
'''
    if n<15:s+=f'  apply congrArg (fun finish => internal_sum_step12 state part_sum {n}#usize >>= finish)\n  funext next\n  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using internal_sum_fold12_{n+1:02} state old_zero next\n'
    else:s+='  rfl\n'
    s+=f'#print axioms internal_sum_cell12_{n:02}\n#print axioms internal_sum_fold12_{n:02}\nend PV_B3P_Binding12227\n';files[mod]=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/internal-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
