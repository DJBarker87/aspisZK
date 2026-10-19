import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-! Exact two-point fibers of the accepted M31 word mask.  This generic
arithmetic leaf intentionally avoids the heavyweight R1 privacy imports;
the later consumer identifies `mask31 < P31` with CommitReadsR1's `!rejB`.
No 2^32-word enumeration occurs. -/
set_option autoImplicit false
namespace M31AcceptFiber

abbrev Word := Fin (2 ^ 32)
def P31 : Nat := 2 ^ 31 - 1
def mask31 (w : Word) : Nat := w.val &&& 0x7fffffff

theorem mask31_eq_mod (w : Word) : mask31 w = w.val % 2 ^ 31 := by
  unfold mask31
  rw [show (0x7fffffff : Nat) = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem add_modulus (r : Nat) (hr : r < 2 ^ 31) :
    (r + 2 ^ 31) % 2 ^ 31 = r := by
  omega

/-- A valid masked M31 value has exactly the two 32-bit preimages
`r` and `r + 2^31`. -/
theorem accepted_fiber_card (r : Fin P31) :
    (Finset.univ.filter (fun w : Word => mask31 w = r.val)).card = 2 := by
  let w0 : Word := ⟨r.val, by
    have hr := r.isLt
    unfold P31 at hr
    omega⟩
  let w1 : Word := ⟨r.val + 2 ^ 31, by
    have hr := r.isLt
    unfold P31 at hr
    omega⟩
  have hrsmall : r.val < 2 ^ 31 := by
    have hr := r.isLt
    unfold P31 at hr
    omega
  have hmod0 : w0.val % 2 ^ 31 = r.val := by
    change r.val % 2 ^ 31 = r.val
    exact Nat.mod_eq_of_lt hrsmall
  have hmod1 : w1.val % 2 ^ 31 = r.val := by
    simpa [w1] using add_modulus r.val hrsmall
  have hmask0 : mask31 w0 = r.val := by rw [mask31_eq_mod, hmod0]
  have hmask1 : mask31 w1 = r.val := by rw [mask31_eq_mod, hmod1]
  have hneq : w0 ≠ w1 := by
    intro h
    have := congrArg Fin.val h
    simp only [w0, w1, Fin.mk.injEq] at this
    omega
  have hset : Finset.univ.filter (fun w : Word => mask31 w = r.val) = {w0, w1} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hmask
      have hmod : w.val % 2 ^ 31 = r.val := by
        rw [← mask31_eq_mod]
        exact hmask
      have hdiv : w.val / 2 ^ 31 < 2 := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 31)).2
        have hw := w.isLt
        norm_num at hw ⊢
        omega
      have hdecomp : w.val % 2 ^ 31 + 2 ^ 31 * (w.val / 2 ^ 31) = w.val :=
        Nat.mod_add_div _ _
      have hq : w.val / 2 ^ 31 = 0 ∨ w.val / 2 ^ 31 = 1 := by omega
      rcases hq with hq | hq
      · left
        apply Fin.ext
        rw [← hdecomp, hmod, hq]
        simp [w0]
      · right
        apply Fin.ext
        rw [← hdecomp, hmod, hq]
        simp [w1]
    · intro h
      rcases h with h | h
      · subst w
        exact hmask0
      · subst w
        exact hmask1
  rw [hset]
  simp [hneq]

#print axioms accepted_fiber_card

end M31AcceptFiber
