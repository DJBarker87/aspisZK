import RPv_FJb_ColumnRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnTable
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FJb_ColumnRow (Row)
open FJb_ColumnCell (atWord)
abbrev Table := Array Row 4#usize
abbrev callback := state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
abbrev call := state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut

theorem callback_total (s : State) (c : Usize) (hc : c.val < 4) :
    ∃ row : Row,call s c=ok (row,s) := by
  obtain ⟨row,hr⟩ := FJb_ColumnRow.total s c hc
  refine ⟨row,?_⟩
  change (do let row ← array_from_fn_copy 4#usize core.marker.CopyU64 FJb_ColumnRow.callback 0#u64 (s,c);ok (row,s))=ok (row,s)
  rw [hr,bind_tc_ok]

theorem value (s : State) (out : Table)
    (run : array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      callback (Array.repeat 4#usize 0#u64) s=ok out) :
    ∀ (c : Usize) (hc : c.val < (4#usize).val) (i : Usize) (hi : i.val < (4#usize).val),
      let row := out.val[c.val]'(by simpa only [out.property] using hc)
      (row.val[i.val]'(by simpa only [row.property] using hi)).val=
        (atWord s c.val i hi).val+(atWord s (4+c.val) i hi).val+
          (atWord s (8+c.val) i hi).val+(atWord s (12+c.val) i hi).val ∧
      (row.val[i.val]'(by simpa only [row.property] using hi)).val < 2^34 := by
  have selected := FJb_BuilderSelected.value 4#usize
    (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) callback
    (Array.repeat 4#usize 0#u64) s (fun c hc=>callback_total s c hc) out run
  intro c hc i hi
  have called := selected c hc
  change (do
    let row ← array_from_fn_copy 4#usize core.marker.CopyU64 FJb_ColumnRow.callback 0#u64 (s,c)
    ok (row,s))=ok (_,s) at called
  obtain ⟨row,hrow,called⟩ := FIv_Map.bind_success _ _ _ called
  have he := (Prod.mk.inj (Result.ok.inj called)).1
  subst row
  exact FJb_ColumnRow.value s c hc _ hrow i hi
#print axioms callback_total
#print axioms value
end AspisR1.FJb_ColumnTable
end
