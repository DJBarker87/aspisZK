import NDO_JFu_TerminalCallback
import RPv_FJb_BuilderSelected
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_SelectedCells
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (cells)
abbrev Selected := Array field.QM31 84#usize
abbrev builder := pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

def expected (i : Fin (84#usize).val) : field.QM31 :=
  let row := JFu_TerminalCallback.claims.val[i.val/28]'(by rw [JFu_TerminalCallback.claims.property];have h:=i.isLt;change i.val<84 at h;change i.val/28<3;omega)
  row.val[i.val%28]'(by rw [row.property];have h:=Nat.mod_lt i.val (by decide : 0<28);change i.val%28<29;omega)

theorem callback (i : Usize) (hi : i.val<(84#usize).val) :
    builder.call_mut JFu_TerminalCallback.claims i=ok (expected ⟨i.val,hi⟩,JFu_TerminalCallback.claims) := by
  have spec : builder.call_mut JFu_TerminalCallback.claims i ⦃ out=>
      out=(expected ⟨i.val,hi⟩,JFu_TerminalCallback.claims) ⦄ := by
    dsimp only [builder]
    unfold pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut expected
    step* <;> scalar_tac
  obtain ⟨out,run,rfl⟩ := WP.spec_imp_exists spec
  exact run
#print axioms callback

theorem value (selected : Selected)
    (run : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy builder field.QM31.ZERO
      JFu_TerminalCallback.claims=ok selected) (i : Fin (84#usize).val) :
    cells selected i=expected i := by
  let u : Usize := Usize.ofNatCore i.val (lt_trans i.isLt (84#usize).hBounds)
  have hi : u.val<(84#usize).val := i.isLt
  have selectedCall := FJb_BuilderSelected.value 84#usize field.QM31.Insts.CoreMarkerCopy builder
    field.QM31.ZERO JFu_TerminalCallback.claims JFu_TerminalCallback.source selected run u hi
  have same := Prod.mk.inj (Result.ok.inj (selectedCall.symm.trans (callback u hi)))
  exact same.1
#print axioms value
end AspisR1.JGl_SelectedCells
end
