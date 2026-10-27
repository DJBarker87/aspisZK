import XRv_SelectedAdvance
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRv_DriverSelected
open XRv_QueryDriver XRv_QueryDriverTotal

theorem selected (blocks advances : Blocks) (out : State)
 (run : (List.range 8).foldlM (step blocks advances)
   ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8)) = ok out) :
 ∃ i, i<8 ∧ Array.index_usize advances (XRn_Join_usize i) = ok out.2.2.2 := by
 rcases XRv_SelectedAdvance.fold_selected blocks advances (List.range 8)
   (fun i hi => List.mem_range.mp hi) _ out run with hs | ⟨i,hi,hr⟩
 · refine ⟨7,by omega,?_⟩
   have hlen : advances.val.length = 8 := advances.property
   have hidx : 7 < advances.val.length := by omega
   rw [index advances 7 (by omega),hs,List.getElem?_eq_getElem hidx]
   rfl
 · exact ⟨i,List.mem_range.mp hi,hr⟩

#print axioms selected
end XRv_DriverSelected
