import XRy_QueryTransport
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRy_Remainder

theorem canonical (x : U32) : ∃ z,
 x % 2147483647#u32 = ok z ∧ z.val < 2147483647 ∧
 z % 2147483647#u32 = ok z := by
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
   (UScalar.rem_spec x (y:=2147483647#u32) (by scalar_tac))
 have hv' : z.val = x.val % 2147483647 := hv
 have hp : z.val < 2147483647 := by rw [hv']; exact Nat.mod_lt _ (by omega)
 obtain ⟨w,hw,hwv⟩ := WP.spec_imp_exists
   (UScalar.rem_spec z (y:=2147483647#u32) (by scalar_tac))
 have hwv' : w.val = z.val % 2147483647 := hwv
 have he : w=z := UScalar.eq_of_val_eq (hwv'.trans (Nat.mod_eq_of_lt hp))
 exact ⟨z,hz,hp,he ▸ hw⟩

#print axioms canonical
end XRy_Remainder
