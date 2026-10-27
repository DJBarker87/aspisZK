import XRo_Join_Installed
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_CheckedWrapping

theorem add (a b : U32) (h : a.val + b.val < 4294967296) :
    a + b = ok (U32.wrapping_add a b) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
  have hw := UScalar.wrapping_add_val_eq a b
  change (U32.wrapping_add a b).val = (a.val+b.val) % 4294967296 at hw
  rw [Nat.mod_eq_of_lt h] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

theorem sub (a b : U32) (h : b.val ≤ a.val) :
    a - b = ok (U32.wrapping_sub a b) := by
  obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=a) (y:=b) h)
  have hw := UScalar.wrapping_sub_val_eq a b
  change (U32.wrapping_sub a b).val = (a.val+(4294967296-b.val)) % 4294967296 at hw
  have hb : b.val ≤ 4294967295 := by scalar_tac
  have ha : a.val ≤ 4294967295 := by scalar_tac
  have he : a.val + (4294967296-b.val) = 4294967296 + (a.val-b.val) := by omega
  have hl : a.val-b.val < 4294967296 := by omega
  rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_eq_of_lt hl] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

#print axioms add
#print axioms sub
end XRp_CheckedWrapping
