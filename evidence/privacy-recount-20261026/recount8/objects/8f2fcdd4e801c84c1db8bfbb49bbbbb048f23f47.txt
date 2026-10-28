import R1Z.PV_RDB2_LayoutGuards

/-! The old mem::Alignment and deployed ptr::Alignment both encode their
power-of-two enum discriminant as the allocator's usize argument. The source
binding checks their transparent/usize representation and accessor bodies. -/
namespace R1Z.PV_RDB2_Alignment
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Alignment where
  exponent : Fin 64

def word (a : Alignment) : Nat := 2^a.exponent.val
def oldAsUsize (a : Alignment) : Nat := word a
def deployedAsUsize (a : Alignment) : Nat := 2^a.exponent.val

theorem positive (a : Alignment) : 0 < word a := by
  exact Nat.two_pow_pos _

theorem within_half_word (a : Alignment) : word a ≤ 2^63 := by
  apply Nat.pow_le_pow_right (by omega)
  have := a.exponent.isLt
  omega

theorem allocator_argument (a : Alignment) : oldAsUsize a = deployedAsUsize a := rfl

theorem nonzero_accessor_complete {World : Type} (a : Alignment) (world : World) :
    (ok (oldAsUsize a,world) : Result (Nat × World)) =
      ok (deployedAsUsize a,world) := rfl

theorem max_size_transport (halfWord : Nat) (a : Alignment) :
    PV_RDB2_LayoutGuards.maximum halfWord (oldAsUsize a) =
      PV_RDB2_LayoutGuards.maximum halfWord (deployedAsUsize a) := rfl

#print axioms positive
#print axioms within_half_word
#print axioms allocator_argument
#print axioms nonzero_accessor_complete
#print axioms max_size_transport
end R1Z.PV_RDB2_Alignment
