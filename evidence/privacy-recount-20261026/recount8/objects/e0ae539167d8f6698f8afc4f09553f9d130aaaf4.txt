import R1Z.ProverRwP6PowersSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersCongruence
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

theorem body (left right : ExternalFuns) {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize)
    (mul : ∀ a b, left.op47 a b = right.op47 a b) :
    @ProverRwP6PowersSource.weights.powers_loop.body _ left N x out p i =
      @ProverRwP6PowersSource.weights.powers_loop.body _ right N x out p i := by
  unfold ProverRwP6PowersSource.weights.powers_loop.body
  simp only [ProverRwFull.aspis_core.field.wide_exact.WideExact.mul, mul]

theorem loop (left right : ExternalFuns) {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize)
    (mul : ∀ a b, left.op47 a b = right.op47 a b) :
    @ProverRwP6PowersSource.weights.powers_loop _ left N x out p i =
      @ProverRwP6PowersSource.weights.powers_loop _ right N x out p i := by
  unfold ProverRwP6PowersSource.weights.powers_loop
  congr 1
  funext state
  exact body left right x state.1 state.2.1 state.2.2 mul

theorem powers (left right : ExternalFuns) (N : Usize) (x : W)
    (zero : left.op42 = right.op42) (one : left.op91 = right.op91)
    (mul : ∀ a b, left.op47 a b = right.op47 a b) :
    @ProverRwP6PowersSource.weights.powers _ left N x =
      @ProverRwP6PowersSource.weights.powers _ right N x := by
  unfold ProverRwP6PowersSource.weights.powers
  simp only [ProverRwFull.aspis_core.field.wide_exact.WideExact.ZERO,
    ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE,
    ProverRwFull.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE]
  rw [zero,one]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro z hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro o ho
  rw [loop left right x (Array.repeat N z) o 0#usize mul]
#print axioms body
#print axioms loop
#print axioms powers
end R1Z.ProverRwP6PowersCongruence
