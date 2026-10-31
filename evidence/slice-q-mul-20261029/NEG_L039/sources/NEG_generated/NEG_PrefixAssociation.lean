import NEG_PrefixFull.Funs
set_option autoImplicit false
noncomputable section
namespace NEG_PrefixAssociation
open Aeneas Aeneas.Std Result ControlFlow AspisR1

def ops : Port4C_NativePrefix.Leaves :=
  ⟨AspisR1Qm31ArithmeticProbe.field.M31.mul,ok 1#u32⟩

theorem guarded_increment (index len : Usize) (h : index < len) :
    (index + 1#usize : Result Usize) = ok (UScalar.wrapping_add index 1#usize) := by
  have hm : index.val + (1#usize).val ≤ UScalar.max .Usize := by scalar_tac
  obtain ⟨z,run,hz⟩ := WP.spec_imp_exists (UScalar.add_spec hm)
  have eq : z = UScalar.wrapping_add index 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.wrapping_add_val_eq,hz]
    have hlt : index.val + (1#usize).val < UScalar.size .Usize := by
      change index.val + (1#usize).val < 2^UScalarTy.Usize.numBits
      have hp : 0 < 2^UScalarTy.Usize.numBits := Nat.pow_pos (by decide)
      change index.val + (1#usize).val ≤ 2^UScalarTy.Usize.numBits-1 at hm
      omega
    exact (Nat.mod_eq_of_lt hlt).symm
  rw [eq] at run
  exact run

theorem step (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) :
    NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop.body ops flat prefixes product index := by
  unfold NEG_PrefixFull.batch_prefix_products_loop.body
    Port4C_NativePrefix.verifier.batch_prefix_products_loop.body
  by_cases active : index < Slice.len flat
  · simp only [active,if_true,ops]
    rw [guarded_increment index (Slice.len flat) active]
    rfl
  · simp only [active,if_false]

theorem loop (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) :
    NEG_PrefixFull.batch_prefix_products_loop flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop ops flat prefixes product index := by
  unfold NEG_PrefixFull.batch_prefix_products_loop
    Port4C_NativePrefix.verifier.batch_prefix_products_loop
  congr 1
  funext state
  rcases state with ⟨p,v,i⟩
  exact step flat p v i

theorem source (flat : Slice U32) :
    NEG_PrefixFull.batch_prefix_products flat =
      Port4C_NativePrefix.verifier.batch_prefix_products ops flat := by
  unfold NEG_PrefixFull.batch_prefix_products
    Port4C_NativePrefix.verifier.batch_prefix_products
  simp only [NEG_PrefixFull.aspis_core.field.M31.ONE,ops,bind_tc_ok]
  exact loop flat _ _ _

#print axioms guarded_increment
#print axioms step
#print axioms loop
#print axioms source
end NEG_PrefixAssociation
end
