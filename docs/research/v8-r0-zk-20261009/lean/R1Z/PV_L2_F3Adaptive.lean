import R1Z.PV_L2_F3Words
import R1Z.CouplingR1PBin

/-! Adaptive raw-word equivalence: each accepted logical scalar can have
its own permutation. The index advances only on acceptance, so rejected
prefixes keep both their positions and the future scalar permutation.
No enormous word space is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Adaptive
open R1Z.PV_L2_F3Words
attribute [local instance] Classical.propDecidable
abbrev Relabel := Nat → (Fin 2147483647 ≃ Fin 2147483647)

def nextIndex (index : Nat) (c : Candidate) := index + if accepts c then 1 else 0

theorem index_preserved (e : Fin 2147483647 ≃ Fin 2147483647)
    (index : Nat) (c : Candidate) : nextIndex index (permute e c) = nextIndex index c := by
  simp only [nextIndex, propext (accepts_permute e c)]

def relabel (e : Relabel) : (n : Nat) → Nat → (Fin n → Candidate) → (Fin n → Candidate)
  | 0, _, w => w
  | n+1, index, w => Fin.cons (permute (e index) (w 0))
      (relabel e n (nextIndex index (w 0)) (Fin.tail w))

theorem permute_inverse (e : Fin 2147483647 ≃ Fin 2147483647) (c : Candidate) :
    permute e.symm (permute e c) = c := by
  unfold permute
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Equiv.optionCongr_apply, Option.map_map]
  have he : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  rw [he]
  simp only [Option.map_id, id_eq, Equiv.symm_apply_apply]

theorem relabel_inverse (e : Relabel) (n index : Nat) (w : Fin n → Candidate) :
    relabel (fun j => (e j).symm) n index (relabel e n index w) = w := by
  induction n generalizing index with
  | zero => rfl
  | succ n ih =>
    simp only [relabel, Fin.cons_zero, Fin.tail_cons, index_preserved, permute_inverse, ih]
    exact Fin.cons_self_tail w

def streamEquiv (e : Relabel) (n index : Nat) : (Fin n → Candidate) ≃ (Fin n → Candidate) where
  toFun := relabel e n index
  invFun := relabel (fun j => (e j).symm) n index
  left_inv := relabel_inverse e n index
  right_inv := by
    intro w
    have hh := relabel_inverse (fun j => (e j).symm) n index w
    simpa only [Equiv.symm_symm] using hh

theorem acceptance_history (e : Relabel) (n index : Nat) (w : Fin n → Candidate) :
    (fun i => decide (accepts (streamEquiv e n index w i))) =
      (fun i => decide (accepts (w i))) := by
  induction n generalizing index with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [streamEquiv, Equiv.coe_fn_mk, relabel, Fin.cons_zero,
        propext (accepts_permute _ _)]
    · exact congrFun (ih (nextIndex index (w 0)) (Fin.tail w)) j

/-- Exact uniform finite input law, including the rejected suffix; high bits
can be carried by an independent product equivalence without modification. -/
theorem uniform_transport (e : Relabel) (n index : Nat)
    (test : (Fin n → Candidate) → ℚ) :
    R0Z.mean (fun w => test (streamEquiv e n index w)) = R0Z.mean test :=
  R1Z.CouplingR1PBin.mp_equiv (streamEquiv e n index) test

#print axioms index_preserved
#print axioms permute_inverse
#print axioms relabel_inverse
#print axioms streamEquiv
#print axioms acceptance_history
#print axioms uniform_transport
end R1Z.PV_L2_F3Adaptive
