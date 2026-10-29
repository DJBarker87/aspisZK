"""Bind the actual preweighted constructor before the inclusive group loop.
Four guarded windows are kept as opaque Result computations, not case-split.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 Result\nset_option autoImplicit false\n'
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
decl=re.search(r'^def reference_terminal.add_preweighted_loop.body\b[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
code=decl[decl.index('    let output :='):decl.index('    let q4 ← Array.index_usize packed')]
code='\n'.join(line[2:] for line in code.rstrip().splitlines())+'\n  .ok output4\n'
params='''{N : Usize} (start : Usize) (values : Array aspis_core.field.QM31 N)
    (group_index : Usize)'''
s='import PV_B3P_BindBranch12227\nimport PV_B3P_Ordered227\nimport PV_B3P_P227_08\nimport PV_B3P_FourStores12227\nimport PV_B3P_DigestCpsEq9227\n'+h+'''
def preweighted_window12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (group_index slot : Usize) :
    Result aspis_core.field.QM31 := do
  let base ← lift (Usize.wrapping_mul 4#usize group_index)
  let source ← lift (Usize.wrapping_add base slot)
  if source >= start then
    let stop ← lift (Usize.wrapping_add start N)
    if source < stop then
      let offset ← lift (Usize.wrapping_sub source start)
      Array.index_usize values offset
    else .ok aspis_core.field.QM31.ZERO
  else .ok aspis_core.field.QM31.ZERO
'''
s+=f'\ndef preweighted_build_stores12 {params} : Result (Array aspis_core.field.QM31 4#usize) := do\n'+code
s+='attribute [local irreducible] Array.index_usize Usize.wrapping_mul Usize.wrapping_add Usize.wrapping_sub\n'
s+=f'''theorem preweighted_build_binding12 {params} :
    preweighted_build_stores12 start values group_index =
      four_build12 (preweighted_window12 start values group_index) := by
  simpa only [preweighted_build_stores12,preweighted_window12,lift,bind_tc_ok,
    PV_B3P_Ordered227.bind_assoc,bind_branch12,bind_return12] using
    four_interleaved12 aspis_core.field.QM31.ZERO (preweighted_window12 start values group_index)
#print axioms preweighted_build_binding12
end PV_B3P_Binding12227
'''
files['PV_B3P_PreweightedBuild12227']=s
s='import PV_B3P_PreweightedBuild12227\n'+h+'''
def preweighted_source_step12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (packed : Array aspis_core.field.QM31 24#usize) (group_index : Usize) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let lanes ← four_build12 (preweighted_window12 start values group_index)
  let old ← Array.index_usize packed group_index
  let slice ← lift (Array.to_slice lanes)
  let value ← host_terminal_field.qm31_pack_base4 slice
  let next ← aspis_core.field.QM31.add old value
  Array.update packed group_index next

attribute [local irreducible] Array.index_usize Array.update host_terminal_field.qm31_pack_base4 aspis_core.field.QM31.add Usize.wrapping_add Usize.wrapping_mul Usize.wrapping_sub

theorem preweighted_step_binding12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (last : Usize)
    (packed : Array aspis_core.field.QM31 24#usize) (group_index : Usize) :
    reference_terminal.add_preweighted_loop.body start values last packed group_index =
      (if group_index <= last then do
        let next ← preweighted_source_step12 start values packed group_index
        .ok (.cont (next,Usize.wrapping_add group_index 1#usize))
      else .ok (.done packed)) := by
  unfold preweighted_source_step12
  rw [← preweighted_build_binding12]
  simp only [reference_terminal.add_preweighted_loop.body,preweighted_build_stores12,
    lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc,bind_branch12,bind_return12]

#print axioms preweighted_step_binding12
end PV_B3P_Binding12227
'''
files['PV_B3P_PreweightedStep12227']=s
for m,s in files.items():
    p=L/(m+'.lean')
    if '--check'in sys.argv:assert p.read_text()==s,m
    else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/preweighted-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
