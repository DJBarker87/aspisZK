import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.Pi

/-! Fixed public mixing of existing coins, not an additional hiding axiom. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
open Polynomial
variable {F : Type*} [Field F] {n : ℕ}

noncomputable def coinPolynomial (u : Fin n → F) : F[X] :=
  ∑ i, monomial i.val (u i)

theorem coinPolynomial_coeff (u : Fin n → F) (i : Fin n) :
    (coinPolynomial u).coeff i.val = u i := by
  simp [coinPolynomial, coeff_monomial, ← Fin.ext_iff]

theorem coinPolynomial_degree (u : Fin (n+1) → F) :
    (coinPolynomial u).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)

noncomputable def mix (nodes : Fin n → F) (u : Fin n → F) : Fin n → F :=
  fun i => (coinPolynomial u).eval (nodes i)

theorem mix_apply (nodes : Fin n → F) (u : Fin n → F) (i : Fin n) :
    mix nodes u i = ∑ j, u j * nodes i ^ j.val := by
  simp [mix, coinPolynomial, eval_finsetSum, eval_monomial]

theorem mix_injective (nodes : Fin n → F) (hinj : Function.Injective nodes) :
    Function.Injective (mix nodes) := by
  cases n with
  | zero => intro u v _; funext i; exact Fin.elim0 i
  | succ n =>
    intro u v h
    have he := eq_of_natDegree_lt_card_of_eval_eq (coinPolynomial u)
      (coinPolynomial v) hinj (fun i => congrFun h i)
      (by simpa only [Fintype.card_fin] using
        (Nat.lt_succ_of_le (max_le (coinPolynomial_degree u) (coinPolynomial_degree v))))
    funext i
    have hc := congrArg (fun p : F[X] => p.coeff i.val) he
    simpa only [coinPolynomial_coeff] using hc

/- The finite-field route avoids importing the much larger nonsingular
matrix inverse dependency. Injectivity and finiteness give the same exact
bijection; no numerical matrix inversion or new cryptographic premise. -/
noncomputable def mixingEquiv (nodes : Fin n → F)
    (hinj : Function.Injective nodes) [Finite F] : (Fin n → F) ≃ (Fin n → F) :=
  Equiv.ofBijective (mix nodes) ⟨mix_injective nodes hinj,
    Finite.surjective_of_injective (mix_injective nodes hinj)⟩

def publicNodes (F : Type*) [Field F] (n : ℕ) (i : Fin n) : F := (i.val + 1 : ℕ)

theorem publicNodes_injective (p : ℕ) [CharP F p] (hn : n < p) :
    Function.Injective (publicNodes F n) := by
  intro i j h
  have e := (CharP.cast_eq_iff_mod_eq F p).mp h
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt i.isLt hn),
    Nat.mod_eq_of_lt (lt_of_le_of_lt j.isLt hn)] at e
  exact Fin.ext (Nat.succ.inj e)

/-- Applicable to QM31's characteristic once its field implementation is
refined; this theorem itself is over an abstract field of that characteristic. -/
noncomputable def mixing1024 [Finite F] [CharP F 2147483647] :
    (Fin 1024 → F) ≃ (Fin 1024 → F) :=
  mixingEquiv (publicNodes F 1024) (publicNodes_injective 2147483647 (by decide))

#print axioms mixingEquiv
#print axioms mix_apply
#print axioms mix_injective
#print axioms publicNodes_injective
#print axioms mixing1024
end AspisV8R17
