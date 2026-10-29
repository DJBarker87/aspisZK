"""Factor the actual eight-lane leading-pair source loop into named cells.
No field arithmetic is reduced; the two following full rounds stay opaque.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
decl=re.search(r'^def reference_poseidon.leading_pair_packed\b[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
lines=decl.split(':= do\n',1)[1].strip('\n').splitlines()
ends=[i+1 for i,l in enumerate(lines) if re.match(r'  let state\d* ← Array.update',l)]
assert len(ends)==8
base='PV_B3P_LeadingStep12227'
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 Result\nset_option autoImplicit false\n'
s='import PV_B3P_P227_08\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+h+'''
abbrev LeadingState12 := Array aspis_core.field.QM31 16#usize
def leading_step12 (xor_values : LeadingState12) (state : LeadingState12) (index : Usize) : Result LeadingState12 := do
  let left ← Array.index_usize state index
  let right ← Array.index_usize xor_values index
  let value ← aspis_core.field.QM31.add left right
  Array.update state index value
'''
suffix='\n'.join(lines[ends[-1]:]);suffix=re.sub(r'\bstate7\b','state',suffix)
s+='\ndef leading_finish12 (state : LeadingState12) : Result (Array aspis_core.field.QM31 4#usize) := do\n'+suffix+'\nend PV_B3P_Binding12227\n'
files[base]=s
for n in reversed(range(8)):
    mod=f'PV_B3P_LeadingCell12{n}227'
    prev=f'PV_B3P_LeadingCell12{n+1}227' if n<7 else base
    incoming='openings.z' if n==0 else 'state'+(str(n-1) if n>1 else '')
    tail='\n'.join(lines[0 if n==0 else ends[n-1]:])
    tail=tail.replace(incoming,'state')
    params='(openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12)'
    nxt=f'leading_tail12_{n+1} openings' if n<7 else 'leading_finish12'
    s=f'import {prev}\n'+h
    s+=f'\ndef leading_tail12_{n} {params} : Result (Array aspis_core.field.QM31 4#usize) := do\n'+tail+'\n'
    s+='attribute [local irreducible] aspis_core.field.QM31.add Array.index_usize Array.update leading_step12 leading_finish12'+(f' leading_tail12_{n+1}' if n<7 else '')+'\n'
    s+=f'''theorem leading_cell12_{n} {params} :
    leading_tail12_{n} openings state =
      (leading_step12 openings.xor12_z state {n}#usize >>= {nxt}) := by
  unfold leading_tail12_{n}
  conv_rhs => simp only [leading_step12,PV_B3P_Ordered227.bind_assoc]
'''
    for j in range(3):s+=f'  apply PV_B3P_Binding9227.bind_equal9\n  intro v{j}\n'
    s+='  apply PV_B3P_Binding9227.bind_equal9\n  intro next\n'
    s+=('  unfold leading_tail12_'+str(n+1)+'\n' if n<7 else '  unfold leading_finish12\n')+'  rfl\n'
    s+=f'''theorem leading_fold12_{n} {params} :
    leading_tail12_{n} openings state =
      (PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
        [{', '.join(str(i)+'#usize' for i in range(n,8))}] state >>= leading_finish12) := by
  rw [leading_cell12_{n}]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
'''
    if n<7:
        s+='  apply congrArg (fun f => leading_step12 openings.xor12_z state '+str(n)+'#usize >>= f)\n  funext next\n  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using leading_fold12_'+str(n+1)+' openings next\n'
    else:s+='  rfl\n'
    s+=f'#print axioms leading_cell12_{n}\n#print axioms leading_fold12_{n}\nend PV_B3P_Binding12227\n'
    files[mod]=s
s='import PV_B3P_LeadingCell120227\n'+h+'''
theorem leading_pair_packed_binding12
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    reference_poseidon.leading_pair_packed openings =
      (PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
        openings.z >>= leading_finish12) :=
  leading_fold12_0 openings openings.z
#print axioms leading_pair_packed_binding12
end PV_B3P_Binding12227
'''
files['PV_B3P_LeadingBinding12227']=s
for m,s in files.items():
    p=L/(m+'.lean')
    if '--check' in sys.argv:assert p.read_text()==s,m
    else:p.write_text(s)
if '--check' not in sys.argv:(D/'resume12/leading-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
