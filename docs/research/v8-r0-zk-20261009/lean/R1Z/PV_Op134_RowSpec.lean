import R1Z.PV_Op134_Rows00
import R1Z.PV_Op134_Rows01
import R1Z.PV_Op134_Rows02
import R1Z.PV_Op134_Rows03
import R1Z.PV_Op134_Rows04
import R1Z.PV_Op134_Rows05
import R1Z.PV_Op134_Rows06
import R1Z.PV_Op134_Rows07
import R1Z.PV_Op134_Rows08
import R1Z.PV_Op134_Rows09
import R1Z.PV_Op134_Rows10
import R1Z.PV_Op134_Rows11
import R1Z.PV_Op134_Rows12
import R1Z.PV_Op134_Rows13
import R1Z.PV_CBM_RowsSelection
namespace R1Z.PV_Op134_RowSpec
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := PV_Op134_Rows00.rows ++
  PV_Op134_Rows01.rows ++
  PV_Op134_Rows02.rows ++
  PV_Op134_Rows03.rows ++
  PV_Op134_Rows04.rows ++
  PV_Op134_Rows05.rows ++
  PV_Op134_Rows06.rows ++
  PV_Op134_Rows07.rows ++
  PV_Op134_Rows08.rows ++
  PV_Op134_Rows09.rows ++
  PV_Op134_Rows10.rows ++
  PV_Op134_Rows11.rows ++
  PV_Op134_Rows12.rows ++
  PV_Op134_Rows13.rows
theorem source (out : alloc.vec.Vec U16) :
    PV_CBM_RowsRaw.reference.fill_rows out = (do
      let next ← PV_CBM_PushList.pushList rows out
      ok (.Ok (),next)) := by rfl

theorem length : rows.length = 214 := by
  simp only [rows,List.length_append,PV_Op134_Rows00.length,PV_Op134_Rows01.length,PV_Op134_Rows02.length,PV_Op134_Rows03.length,PV_Op134_Rows04.length,PV_Op134_Rows05.length,PV_Op134_Rows06.length,PV_Op134_Rows07.length,PV_Op134_Rows08.length,PV_Op134_Rows09.length,PV_Op134_Rows10.length,PV_Op134_Rows11.length,PV_Op134_Rows12.length,PV_Op134_Rows13.length]

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
#print axioms source
#print axioms length
#print axioms run
#print axioms callback
end R1Z.PV_Op134_RowSpec
