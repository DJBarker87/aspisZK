import NDN_Reference1.Funs
import NDN_Reference4.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_CoordinateBridge
theorem coordinate (mask : U16)
 (hm : mask = 6144#u16 ∨ mask = 6145#u16 ∨ mask = 4097#u16 ∨ mask = 2048#u16 ∨ mask = 2049#u16 ∨ mask = 26214#u16 ∨ mask = 1749#u16) :
 ∃ i, NDN_Reference1.active_coordinate mask=ok i ∧ i.val<7 := by
 rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact ⟨0#usize,rfl,by decide⟩
 · exact ⟨1#usize,rfl,by decide⟩
 · exact ⟨2#usize,rfl,by decide⟩
 · exact ⟨3#usize,rfl,by decide⟩
 · exact ⟨4#usize,rfl,by decide⟩
 · exact ⟨5#usize,rfl,by decide⟩
 · exact ⟨6#usize,rfl,by decide⟩

theorem count (c : Usize) (hc:c.val<7) :
 ∃ n,NDN_Reference4.low_count c=ok n ∧ 0<n.val ∧ n.val≤8 := by
 have h : c.val=0 ∨ c.val=1 ∨ c.val=2 ∨ c.val=3 ∨ c.val=4 ∨ c.val=5 ∨ c.val=6 := by omega
 rcases h with h | h | h | h | h | h | h
 · have e : c=0#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨2#usize,rfl,by decide,by decide⟩
 · have e : c=1#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨3#usize,rfl,by decide,by decide⟩
 · have e : c=2#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨2#usize,rfl,by decide,by decide⟩
 · have e : c=3#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨1#usize,rfl,by decide,by decide⟩
 · have e : c=4#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨2#usize,rfl,by decide,by decide⟩
 · have e : c=5#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨8#usize,rfl,by decide,by decide⟩
 · have e : c=6#usize := UScalar.eq_of_val_eq h
   subst c
   exact ⟨7#usize,rfl,by decide,by decide⟩

#print axioms coordinate
#print axioms count
end NDN_CoordinateBridge
