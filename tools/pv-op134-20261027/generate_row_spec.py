from pathlib import Path
import sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=''.join(f'import R1Z.PV_Op134_Rows{i:02}\n' for i in range(14))
s+='''import R1Z.PV_CBM_RowsSelection
namespace R1Z.PV_Op134_RowSpec
open Aeneas Aeneas.Std Result
set_option autoImplicit false
'''
s+='def rows : List U16 := '+' ++\n  '.join(f'PV_Op134_Rows{i:02}.rows' for i in range(14))+'\n'
s+='''theorem bind_assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (do let b ← (do let a ← r; f a); g b) =
      (do let a ← r; let b ← f a; g b) := by
  cases r <;> rfl

theorem source (out : alloc.vec.Vec U16) :
    PV_CBM_RowsRaw.reference.fill_rows out = (do
      let next ← PV_CBM_PushList.pushList rows out
      ok (.Ok (),next)) := by
  unfold PV_CBM_RowsRaw.reference.fill_rows
  simp only [rows,PV_Op134_Rows00.rows,PV_Op134_Rows01.rows,PV_Op134_Rows02.rows,PV_Op134_Rows03.rows,PV_Op134_Rows04.rows,PV_Op134_Rows05.rows,PV_Op134_Rows06.rows,PV_Op134_Rows07.rows,PV_Op134_Rows08.rows,PV_Op134_Rows09.rows,PV_Op134_Rows10.rows,PV_Op134_Rows11.rows,PV_Op134_Rows12.rows,PV_Op134_Rows13.rows,List.cons_append,List.nil_append,PV_CBM_PushList.pushList,bind_assoc,bind_tc_ok]

theorem length : rows.length = 214 := by
  simp only [rows,List.length_append,'''+','.join(f'PV_Op134_Rows{i:02}.length' for i in range(14))+''']

theorem run (out : alloc.vec.Vec U16) (hc : out.val.length + 214 ≤ 4096) :
    ∃ result, PV_CBM_RowsRaw.reference.fill_rows out = ok (.Ok (),result) ∧
      result.val = out.val ++ rows := by
  obtain ⟨result,hr,hv⟩ := PV_CBM_PushList.pushList_spec rows out (by rw [length]; exact hc)
  exact ⟨result,by rw [source,hr]; rfl,hv⟩

theorem callback : ∃ result : alloc.vec.Vec U16,
    PV_CBM_RowsSelection.callback = ok (.Ok result) ∧ result.val = rows := by
  obtain ⟨result,hr,hv⟩ := run (alloc.vec.Vec.new U16) (by change 0+214≤4096; decide)
  refine ⟨result,?_,?_⟩
  · unfold PV_CBM_RowsSelection.callback
    rw [hr]
    rfl
  · simpa only [alloc.vec.Vec.new,List.nil_append] using hv
#print axioms bind_assoc
#print axioms source
#print axioms length
#print axioms run
#print axioms callback
end R1Z.PV_Op134_RowSpec
'''
p=lean/'PV_Op134_RowSpec.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED','row spec')
