"""Factor the frozen reference computation into small proof-only continuations."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
values=list(map(int,re.findall(r'Vec.push \w+ (\d+)#u16',(lean/'PV_CBM_RowsReference.lean').read_text())))
assert len(values)==214
s=''.join(f'import R1Z.PV_Op134_Rows{i:02}\n' for i in range(14))
s+='''import R1Z.PV_CBM_RowsSelection
namespace R1Z.PV_Op134_RowSpec
open Aeneas Aeneas.Std Result
set_option autoImplicit false
'''
s+='def rows : List U16 := '+' ++\n  '.join(f'PV_Op134_Rows{i:02}.rows' for i in range(14))+'\n'
s+='''abbrev Answer := Result ((core.result.Result Unit PV_CBM_CellsMaterializer.LayoutError) × alloc.vec.Vec U16)
-- Proof-only factoring of the reference extraction, not a native implementation.
def tail14 (out : alloc.vec.Vec U16) : Answer := ok (.Ok (),out)
'''
for i in range(13,-1,-1):
 vs=values[16*i:16*(i+1)]
 s+=f'def tail{i} (out : alloc.vec.Vec U16) : Answer := do\n'
 for j,v in enumerate(vs,1):
  prev='out' if j==1 else f'out{j-1}'
  s+=f'  let out{j} ← alloc.vec.Vec.push {prev} {v}#u16\n'
 s+=f'  tail{i+1} out{len(vs)}\n'
for i in range(14):
 vs=values[16*i:16*(i+1)]
 s+=f'def prefix{i} (f : alloc.vec.Vec U16 → Answer) (out : alloc.vec.Vec U16) : Answer := do\n'
 for j,v in enumerate(vs,1):
  prev='out' if j==1 else f'out{j-1}'
  s+=f'  let out{j} ← alloc.vec.Vec.push {prev} {v}#u16\n'
 s+=f'  f out{len(vs)}\n'
s+='''theorem source (out : alloc.vec.Vec U16) :
    PV_CBM_RowsRaw.reference.fill_rows out = tail0 out := by
  conv_lhs => unfold PV_CBM_RowsRaw.reference.fill_rows
'''
for i in range(14):
 prev='out' if i==0 else f'state{i}'
 s+=f'''  conv_rhs => unfold tail{i}
  apply congrArg (fun f : alloc.vec.Vec U16 → Answer => prefix{i} f {prev})
  funext state{i+1}
'''
s+='''  conv_rhs => unfold tail14
  all_goals rfl

theorem last (out : alloc.vec.Vec U16) : tail14 out = ok (.Ok (),out) := rfl

theorem bind_assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (do let b ← (do let a ← r; f a); g b) =
      (do let a ← r; let b ← f a; g b) := by
  cases r <;> rfl

theorem bind_ok {α β : Type} {r : Result α} {v : α} (h : r = ok v)
    (f : α → Result β) : (do let x ← r; f x) = f v := by
  simp only [h,bind_tc_ok]
'''
s+='attribute [local irreducible] '+' '.join(f'tail{i}' for i in range(15))+'\n'
for i in range(14):
 s+=f'''theorem segment{i} (out : alloc.vec.Vec U16) :
    tail{i} out = (do let next ← PV_CBM_PushList.pushList PV_Op134_Rows{i:02}.rows out; tail{i+1} next) := by
  unfold tail{i}
  simp only [PV_Op134_Rows{i:02}.rows,PV_CBM_PushList.pushList,bind_assoc,bind_tc_ok]
'''
s+='theorem length : rows.length = 214 := by\n  simp only [rows,List.length_append,'+','.join(f'PV_Op134_Rows{i:02}.length' for i in range(14))+']\n'
s+='''theorem run (out : alloc.vec.Vec U16) (hc : out.val.length + 214 ≤ 4096) :
    ∃ result, PV_CBM_RowsRaw.reference.fill_rows out = ok (.Ok (),result) ∧
      result.val = out.val ++ rows := by
  have l0 : out.val.length = out.val.length+0 := by omega
'''
for i in range(14):
 prev='out' if i==0 else f'out{i}';offset=min(16*(i+1),214)
 s+=f'''  obtain ⟨out{i+1},h{i+1},v{i+1}⟩ := PV_CBM_PushList.pushList_spec PV_Op134_Rows{i:02}.rows {prev}
    (by rw [PV_Op134_Rows{i:02}.length]; have h := l{i}; omega)
  have l{i+1} : out{i+1}.val.length = out.val.length+{offset} := by
    rw [v{i+1},List.length_append,PV_Op134_Rows{i:02}.length,l{i}]
    all_goals omega
'''
s+='  have t14 : tail14 out14 = ok (.Ok (),out14) := last out14\n'
for i in range(13,-1,-1):
 prev='out' if i==0 else f'out{i}'
 s+=f'''  have t{i} : tail{i} {prev} = ok (.Ok (),out14) :=
    (segment{i} {prev}).trans ((bind_ok h{i+1} (fun next => tail{i+1} next)).trans t{i+1})
'''
s+='''  refine ⟨out14,(source out).trans t0,?_⟩
  rw ['''+','.join(f'v{i}' for i in range(14,0,-1))+''']
  simp only [rows,List.append_assoc]

theorem callback : ∃ result : alloc.vec.Vec U16,
    PV_CBM_RowsSelection.callback = ok (.Ok result) ∧ result.val = rows := by
  obtain ⟨result,hr,hv⟩ := run (alloc.vec.Vec.new U16) (by change 0+214≤4096; decide)
  refine ⟨result,?_,?_⟩
  · unfold PV_CBM_RowsSelection.callback
    rw [hr]
    rfl
  · simpa only [alloc.vec.Vec.new,List.nil_append] using hv
'''
for n in ['source','last','bind_assoc','bind_ok']+[f'segment{i}' for i in range(14)]+['length','run','callback']:
 s+='#print axioms '+n+'\n'
s+='end R1Z.PV_Op134_RowSpec\n'
p=lean/'PV_Op134_RowSpec.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED','factored row spec')
