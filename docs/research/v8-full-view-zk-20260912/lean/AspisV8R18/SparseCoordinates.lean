import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/- Symbolic arithmetic leaves for the R18 candidate. These do not assert a
seed/oracle law, source rank, compiled-Rust refinement or full privacy. -/
namespace AspisV8R18

def slot (i : Fin 271) : Fin 1023 := ⟨128 + 3 * i.val, by omega⟩

theorem slot_injective : Function.Injective slot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp [slot] at hv
  omega

def selected : Finset (Fin 1023) := Finset.univ.image slot

theorem selected_card : selected.card = 271 := by
  simp [selected, Finset.card_image_of_injective _ slot_injective]

theorem retained_card : selectedᶜ.card = 752 := by
  rw [Finset.card_compl, selected_card]
  simp

theorem retained_characterization (j : Fin 1023) :
    j ∈ selectedᶜ ↔ ¬ ∃ i, slot i = j := by
  classical
  simp [selected]

-- Prove codec identities symbolically before specializing to large Fin sizes.
def Rest {I J : Type*} (f : I → J) := {j : J // ¬ ∃ i, f i = j}

noncomputable def split {I J K : Type*} (f : I → J) (x : J → K) :
    (I → K) × (Rest f → K) := (fun i => x (f i), fun j => x j.val)

noncomputable def join {I J K : Type*} (f : I → J) (c : I → K) (r : Rest f → K)
    (j : J) : K := by
  classical
  exact if h : ∃ i, f i = j then c (Classical.choose h) else r ⟨j, h⟩

theorem join_split {I J K : Type*} (f : I → J) (x : J → K) :
    join f (split f x).1 (split f x).2 = x := by
  classical
  funext j
  simp only [join, split]
  split_ifs with h
  · exact congrArg x (Classical.choose_spec h)
  · rfl

theorem split_join {I J K : Type*} (f : I → J) (hf : Function.Injective f)
    (c : I → K) (r : Rest f → K) :
    split f (join f c r) = (c, r) := by
  classical
  apply Prod.ext
  · funext i
    change join f c r (f i) = c i
    have h : ∃ j, f j = f i := ⟨i, rfl⟩
    simp only [join, dif_pos h]
    exact congrArg c (hf (Classical.choose_spec h))
  · funext j
    change join f c r j.val = r j
    simp only [join, dif_neg j.property]
    rfl

section Pairing
variable {K : Type*} [CommRing K]

theorem shared_pairing {ι : Type*} [Fintype ι]
    (R G A E H : ι → K) (k : K) :
    (Finset.univ.sum fun (i : ι) => R i * A i + G i * (A i - k * E i + k * H i)) =
      (Finset.univ.sum fun (i : ι) => (R i + G i) * A i) -
        k * (Finset.univ.sum fun (i : ι) => G i * E i) +
        k * (Finset.univ.sum fun (i : ι) => G i * H i) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- A genuine invertible transport cancels before evaluation of any selected
-- coefficient functional. Identifying e with the source T remains separate.
theorem sparse_transport_cancel
    (e : (Fin 1023 → K) ≃ₗ[K] (Fin 1023 → K))
    (a : Fin 271 → K) (c : Fin 1023 → K) :
    (∑ i, a i * (e (e.symm c)) (slot i)) = ∑ i, a i * c (slot i) := by
  simp

end Pairing
end AspisV8R18

#print axioms AspisV8R18.slot_injective
#print axioms AspisV8R18.selected_card
#print axioms AspisV8R18.retained_card
#print axioms AspisV8R18.retained_characterization
#print axioms AspisV8R18.join_split
#print axioms AspisV8R18.split_join
#print axioms AspisV8R18.shared_pairing
#print axioms AspisV8R18.sparse_transport_cancel
