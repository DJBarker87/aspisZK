import NHI_ScalarStep
import NHI_PartialIndexExtracted
set_option autoImplicit false
namespace NHI_PartialIndex
open Aeneas Aeneas.Std Result

def index (s j : Usize) : Usize := Usize.wrapping_add (Usize.wrapping_mul 16#usize s) j

theorem value (s j : Usize) (hs : s.val<4) (hj : j.val<16) :
 (index s j).val=16*s.val+j.val ∧ (index s j).val<64 := by
 have size : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have hm : 16*s.val<UScalar.size .Usize := by omega
 have ha : 16*s.val+j.val<UScalar.size .Usize := by omega
 have exactValue : (index s j).val=16*s.val+j.val := by
  unfold index
  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq]
  change ((16*s.val)%UScalar.size .Usize+j.val)%UScalar.size .Usize=16*s.val+j.val
  rw [Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt ha]
 exact ⟨exactValue,by omega⟩

theorem extracted (s j : Usize) :
 NHI_PartialIndexRef.partial_index_ref s j=ok (index s j) := rfl

theorem windows_disjoint (s t j k : Nat) (hs : s<4) (ht : t<4)
 (hj : j<16) (hk : k<16) (different : s≠t) : 16*s+j≠16*t+k := by omega

#print axioms value
#print axioms extracted
#print axioms windows_disjoint
end NHI_PartialIndex
