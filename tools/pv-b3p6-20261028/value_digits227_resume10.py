"""Bind all thirty source digit cells including their repeated immutable read.
Six five-cell applications cover actual emitted/direct stages01–06.
"""
from pathlib import Path
import sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={}
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
s='import PV_B3P_ValueCpsBridge10227\nimport PV_B3P_Ordered227\n'+header+'''
/-- The second deterministic read returns the same value; intervening failure stays. -/
theorem repeated_read_between10 {α β γ : Type} (read : Result α)
    (middle : α → Result β) (finish : β → α → Result γ) :
    (do let x ← read; let y ← middle x; let x' ← read; finish y x') =
    (do let x ← read; let y ← middle x; finish y x) := by
  cases read <;> rfl

theorem ordered_fold_congr10 {α β : Type} (first second : α → β → Result α)
    (h : ∀ state index, first state index=second state index)
    (indices : List β) (initial : α) :
    PV_B3P_Ordered227.fold first indices initial = PV_B3P_Ordered227.fold second indices initial := by
  induction indices generalizing initial with
  | nil => rfl
  | cons index indices ih =>
    simp only [PV_B3P_Ordered227.fold]
    rw [h]
    apply congrArg (fun next => second initial index >>= next)
    funext next
    exact ih next

abbrev DigitRange10 := Array aspis_core.field.QM31 33#usize

def digit_finish10 (range : DigitRange10) (offset : Option Usize) (index : Usize)
    (square original : aspis_core.field.QM31) : Result DigitRange10 := do
  let residual ← aspis_core.field.QM31.sub square original
  let target := match offset with | none => index | some start => Usize.wrapping_add start index
  Array.update range target residual

def digit_source_step10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) : Result DigitRange10 := do
  let original ← Array.index_usize values index
  let square ← aspis_core.field.QM31.square original
  let repeated ← Array.index_usize values index
  digit_finish10 range offset index square repeated

def digit_single_step10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) : Result DigitRange10 := do
  let original ← Array.index_usize values index
  let square ← aspis_core.field.QM31.square original
  digit_finish10 range offset index square original

theorem digit_read_binding10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) :
    digit_source_step10 values offset range index = digit_single_step10 values offset range index :=
  repeated_read_between10 (Array.index_usize values index) aspis_core.field.QM31.square (digit_finish10 range offset index)

theorem digit_fold_read_binding10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (indices : List Usize) (range : DigitRange10) :
    PV_B3P_Ordered227.fold (digit_source_step10 values offset) indices range =
      PV_B3P_Ordered227.fold (digit_single_step10 values offset) indices range :=
  ordered_fold_congr10 _ _ (digit_read_binding10 values offset) indices range
#print axioms repeated_read_between10
#print axioms ordered_fold_congr10
#print axioms digit_read_binding10
#print axioms digit_fold_read_binding10
end PV_B3P_Binding10227
''';files['PV_B3P_DigitRead10227']=s
pp='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10)'''
records=[]
for i in range(1,7):
 field=['z','succ_z','xor12_z'][(i-1)//2];offset=['none','(some 10#usize)','(some 20#usize)'][(i-1)//2];start=0 if i%2 else 5;idx='['+', '.join(f'{j}#usize'for j in range(start,start+5))+']'
 s=f'import PV_B3P_DigitRead10227\nimport PV_B3P_ValueRead9{i:02}227\n'+header
 s+='\nattribute [local irreducible] aspis_core.field.QM31.square aspis_core.field.QM31.sub Array.index_usize Array.update Usize.wrapping_add\n'
 s+=f'''\ntheorem digit_single_stage10_{i:02} {pp} :
    value_direct_stage9_{i:02} packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_single_step10 openings.{field} {offset}) {idx} range
      .ok (selector,next)) := by
  unfold value_direct_stage9_{i:02} value_read_context9_{i:02}
  conv_rhs => simp only [PV_B3P_Ordered227.fold,digit_single_step10,digit_finish10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
'''
 s+='  all_goals rfl\n'
 s+=f'''\ntheorem digit_source_stage_binding10_{i:02} {pp} :
    value_direct_stage9_{i:02} packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_source_step10 openings.{field} {offset}) {idx} range
      .ok (selector,next)) := by
  rw [digit_fold_read_binding10]
  exact digit_single_stage10_{i:02} packed openings selectors selector range
#print axioms digit_single_stage10_{i:02}
#print axioms digit_source_stage_binding10_{i:02}
end PV_B3P_Binding10227
''';m=f'PV_B3P_DigitStage10{i:02}227';files[m]=s;records.append(dict(stage=i,values=field,source_indices=list(range(start,start+5)),module=m,theorem=f'digit_source_stage_binding10_{i:02}'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),applications=records,credit='source digit read/CSE and ordered five-cell stage binding only; remaining value frame/unroll composition separate',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'digit-stage-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
