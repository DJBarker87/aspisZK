"""Reconstruct the two source index loops with named 3x3 read/store laws.
This is symbolic transformation evidence; no native matrix differential is claimed.
"""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result\nset_option autoImplicit false\n'
s='import PV_B3P_IndexSteps9227\nimport PV_B3P_BindBranch12227\nimport PV_B3P_MatrixModel10227\nimport PV_B3P_UsizeLoop9227\n'+h+'''
abbrev Channels12 := Array (Array U32 3#usize) 3#usize
def source_channel12 (left right : Channels12) (component : Usize)
    (sums : Matrix3x3) (channel : Usize) : Result Matrix3x3 := do
  let lrow ← Array.index_usize left component
  let l ← Array.index_usize lrow channel
  let rrow ← Array.index_usize right component
  let r ← Array.index_usize rrow channel
  matrix_cell sums component channel l r

theorem source_channel_binding12 (left right : Channels12) (component channel : Usize)
    (hc : component.val<3) (hk : channel.val<3) (sums : Matrix3x3) :
    source_channel12 left right component sums channel =
      matrix_cell sums component channel
        ((left.val[component.val]'(by rw [left.property]; exact hc)).val[channel.val]'(by
          rw [(left.val[component.val]'(by rw [left.property]; exact hc)).property]; exact hk))
        ((right.val[component.val]'(by rw [right.property]; exact hc)).val[channel.val]'(by
          rw [(right.val[component.val]'(by rw [right.property]; exact hc)).property]; exact hk)) := by
  unfold source_channel12
  rw [PV_B3P_SelectIndex227.index_value left component hc]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value (n:=3#usize) _ channel hk]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value right component hc]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value (n:=3#usize) _ channel hk]
  simp only [bind_tc_ok]

theorem three_loop12 {α : Type} (step : α → Usize → Result α) (state : α) :
    loop (usize_body step 3#usize) (state,0#usize) = (do
      let s0 ← step state 0#usize
      let s1 ← step s0 1#usize
      step s1 2#usize) := by
  rw [usize_loop_plan step 3#usize 0#usize 3 state (by scalar_tac)]
  have h01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
  have h12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := next_exact _ _ rfl
  simp only [usize_plan,h01,h12,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,bind_return12]

def source_component12 (left right : Channels12) (component : Usize) (sums : Matrix3x3) : Result Matrix3x3 :=
  loop (usize_body (source_channel12 left right component) 3#usize) (sums,0#usize)

def source_nested12 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 :=
  loop (usize_body (fun sums component => source_component12 left right component sums) 3#usize) (sums,0#usize)

#print axioms source_channel_binding12
#print axioms three_loop12
end PV_B3P_Binding12227
'''
files['PV_B3P_MatrixNested12227']=s
for c in range(3):
 for k in range(3):
  name=f'source_matrix_cell12_{c}_{k}';mod=f'PV_B3P_MatrixNestedCell12{c}{k}227'
  s='import PV_B3P_MatrixNested12227\n'+h
  s+=f'''theorem {name} (left right : Channels12) (sums : Matrix3x3) :
    source_channel12 left right {c}#usize sums {k}#usize =
      matrix_cell sums {c}#usize {k}#usize (get3_{k} (get3_{c} left)) (get3_{k} (get3_{c} right)) :=
  source_channel_binding12 left right {c}#usize {k}#usize (by change {c}<3; omega) (by change {k}<3; omega) sums
#print axioms {name}
end PV_B3P_Binding12227
''';files[mod]=s
for c in range(3):
 s=''.join(f'import PV_B3P_MatrixNestedCell12{c}{k}227\n' for k in range(3))+h
 s+=f'''theorem source_matrix_row12_{c} (left right : Channels12) (sums : Matrix3x3) :
    source_component12 left right {c}#usize sums = (do
      let s0 ← matrix_cell sums {c}#usize 0#usize (get3_0 (get3_{c} left)) (get3_0 (get3_{c} right))
      let s1 ← matrix_cell s0 {c}#usize 1#usize (get3_1 (get3_{c} left)) (get3_1 (get3_{c} right))
      matrix_cell s1 {c}#usize 2#usize (get3_2 (get3_{c} left)) (get3_2 (get3_{c} right))) := by
  unfold source_component12
  rw [three_loop12]
  simp only [{','.join(f'source_matrix_cell12_{c}_{k}' for k in range(3))}]
#print axioms source_matrix_row12_{c}
end PV_B3P_Binding12227
''';files[f'PV_B3P_MatrixNestedRow12{c}227']=s
s=''.join(f'import PV_B3P_MatrixNestedRow12{c}227\n' for c in range(3))+h
s+='def source_nine12 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 := do\n'
prev='sums'
for c in range(3):
 for k in range(3):
  nxt=f's{c}{k}';s+=f'  let {nxt} ← matrix_cell {prev} {c}#usize {k}#usize (get3_{k} (get3_{c} left)) (get3_{k} (get3_{c} right))\n';prev=nxt
s+='  .ok '+prev+'\n'
s+='''theorem source_nested_binding12 (left right : Channels12) (sums : Matrix3x3) :
    source_nested12 left right sums = source_nine12 left right sums := by
  unfold source_nested12
  rw [three_loop12]
  simp only [source_matrix_row12_0,source_matrix_row12_1,source_matrix_row12_2,
    source_nine12,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,bind_return12]
#print axioms source_nested_binding12
end PV_B3P_Binding12227
''';files['PV_B3P_MatrixNestedBinding12227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/matrix-nested-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
