import AdapterRwModel
set_option autoImplicit false
namespace NFQ_ZeroPrimitives
open Aeneas Aeneas.Std Result WP
/-- Minimal dependency version: actual Aeneas slice read, not a window stand-in. -/
theorem index_read (bytes : Slice U8) (i : Usize) (bound : i.val<bytes.length)
    (byte : U8) (selected : bytes.val[i.val]?=some byte) :
    Slice.index_usize bytes i=ok byte := by
  have spec : Slice.index_usize bytes i ⦃ out => out=byte ⦄ := by
    step*
    simp_all
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

theorem wrap_add (x y : Usize) (small : x.val+y.val≤4096) :
    (Usize.wrapping_add x y).val=x.val+y.val := by
  rw [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have capacity : 4096<UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  omega
#print axioms index_read
#print axioms wrap_add
end NFQ_ZeroPrimitives
