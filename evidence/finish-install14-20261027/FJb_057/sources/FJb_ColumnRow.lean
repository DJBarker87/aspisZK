import FJb_ColumnCell
import FJb_BuilderTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnRow
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FJb_ColumnCell (atWord)
abbrev callback := state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev Row := Array U64 4#usize

theorem total (s : State) (c : Usize) (hc : c.val < 4) :
    ∃ out : Row,array_from_fn_copy 4#usize core.marker.CopyU64 callback 0#u64 (s,c)=ok out := by
  apply FJb_BuilderTotal.value
  intro i hi
  obtain ⟨out,hr,_,_⟩ := FJb_ColumnCell.value s c i hc hi
  exact ⟨out,hr⟩

theorem value (s : State) (c : Usize) (hc : c.val < 4) (out : Row)
    (run : array_from_fn_copy 4#usize core.marker.CopyU64 callback 0#u64 (s,c)=ok out) :
    ∀ (i : Usize) (hi : i.val < (4#usize).val),
      (out.val[i.val]'(by simpa only [out.property] using hi)).val=
        (atWord s c.val i hi).val+(atWord s (4+c.val) i hi).val+
          (atWord s (8+c.val) i hi).val+(atWord s (12+c.val) i hi).val ∧
      (out.val[i.val]'(by simpa only [out.property] using hi)).val < 2^34 := by
  have selected := FJb_BuilderSelected.value 4#usize core.marker.CopyU64 callback 0#u64 (s,c)
    (by intro i hi;obtain ⟨x,hx,_,_⟩ := FJb_ColumnCell.value s c i hc hi;exact ⟨x,hx⟩) out run
  intro i hi
  obtain ⟨x,hx,hv,hb⟩ := FJb_ColumnCell.value s c i hc hi
  have he := (Prod.mk.inj (Result.ok.inj (hx.symm.trans (selected i hi)))).1
  exact he ▸ ⟨hv,hb⟩
#print axioms total
#print axioms value
end AspisR1.FJb_ColumnRow
end
