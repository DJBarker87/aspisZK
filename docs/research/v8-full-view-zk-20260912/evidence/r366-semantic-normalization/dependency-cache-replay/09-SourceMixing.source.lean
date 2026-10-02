import AspisV8R17.Mixing
import AspisV8R17.SourceZeroBoundary

/-! Literal reverse Horner mixing, with the retained complete 1024-coordinate
mixing equivalence. The Rust routine reads only its first 271 coordinates;
that projection is not itself asserted to be a bijection. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def sourceMixHorner (x : F) (cs : List F) : F :=
  cs.reverse.foldl (fun out c => out*x+c) 0

theorem sourceMixHorner_cons (x c : F) (cs : List F) :
    sourceMixHorner x (c::cs) = sourceMixHorner x cs * x + c := by
  simp [sourceMixHorner, List.reverse_cons, List.foldl_append]

theorem sourceMixHorner_eq_sum (n : ℕ) (cs : Fin n → F) (x : F) :
    sourceMixHorner x (List.ofFn cs) = ∑ i, cs i * x^i.val := by
  induction n with
  | zero => simp [sourceMixHorner]
  | succ n ih =>
    rw [List.ofFn_succ, sourceMixHorner_cons, ih]
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    simp only [← mul_assoc, ← Finset.sum_mul]
    exact add_comm _ _

theorem sourceMixHorner_add (n : ℕ) (cs ds : Fin n → F) (x : F) :
    sourceMixHorner x (List.ofFn (fun i => cs i + ds i)) =
      sourceMixHorner x (List.ofFn cs) + sourceMixHorner x (List.ofFn ds) := by
  simp only [sourceMixHorner_eq_sum, add_mul, Finset.sum_add_distrib]

theorem sourceMixHorner_eq_mix {n : ℕ} (nodes : Fin n → F) (cs : Fin n → F) (i : Fin n) :
    sourceMixHorner (nodes i) (List.ofFn cs) = mix nodes cs i := by
  rw [sourceMixHorner_eq_sum, mix_apply]

theorem sourceMixHorner_eq_mixing1024 [Finite F] [CharP F 2147483647]
    (cs : Fin 1024 → F) (i : Fin 1024) :
    sourceMixHorner ((i.val+1 : ℕ) : F) (List.ofFn cs) = mixing1024 cs i := by
  exact sourceMixHorner_eq_mix (publicNodes F 1024) cs i

/-- The actual 271 returned coordinates are the prefix of the same full
invertible transform, not fresh or newly sampled coordinates. -/
theorem source_mixed271_prefix [Finite F] [CharP F 2147483647]
    (cs : Fin 1024 → F) (i : Fin 271) :
    sourceMixHorner ((i.val+1 : ℕ) : F) (List.ofFn cs) =
      mixing1024 cs ⟨i.val, by omega⟩ := by
  exact sourceMixHorner_eq_mixing1024 cs ⟨i.val, by omega⟩

#print axioms sourceMixHorner_cons
#print axioms sourceMixHorner_eq_sum
#print axioms sourceMixHorner_add
#print axioms sourceMixHorner_eq_mix
#print axioms sourceMixHorner_eq_mixing1024
#print axioms source_mixed271_prefix
end AspisV8R17
