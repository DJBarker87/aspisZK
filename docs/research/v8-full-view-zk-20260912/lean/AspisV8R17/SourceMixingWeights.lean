import AspisV8R17.SourceMixing
import AspisV8R17.SourceOriginalWeights

/-! Power-row generation and the nested accumulation in mask_weights.
Coin weights remain explicit: proving their equality to the reverse-round
mask functional is the next, separate source obligation. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def mixingRowLoop (node : F) : ℕ → F → List F
  | 0, _ => []
  | n+1, power => power :: mixingRowLoop node n (power*node)

theorem mixingRowLoop_eq (node : F) (n : ℕ) (power : F) :
    mixingRowLoop node n power = List.ofFn (fun i : Fin n => power*node^i.val) := by
  induction n generalizing power with
  | zero => simp [mixingRowLoop]
  | succ n ih =>
    rw [mixingRowLoop, ih, List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 2
    funext i
    ring

def mixingWeightsFold (terms : List (F × F)) (acc : Fin 1024 → F) : Fin 1024 → F :=
  terms.foldl (fun weights term i => weights i+term.2*term.1^i.val) acc

theorem mixingWeightsFold_eq (terms : List (F × F)) (acc : Fin 1024 → F) (i : Fin 1024) :
    mixingWeightsFold terms acc i = acc i+(terms.map fun t => t.2*t.1^i.val).sum := by
  induction terms generalizing acc with
  | nil => simp [mixingWeightsFold]
  | cons t ts ih =>
    simp only [mixingWeightsFold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [add_assoc]

def sourceMixedWeight (coinWeights : Fin 271 → F) : Fin 1024 → F :=
  mixingWeightsFold (List.ofFn fun i : Fin 271 => (((i.val+1 : ℕ) : F),coinWeights i)) (fun _ => 0)

theorem sourceMixedWeight_eq (coinWeights : Fin 271 → F) (i : Fin 1024) :
    sourceMixedWeight coinWeights i = ∑ j : Fin 271, coinWeights j*((j.val+1 : ℕ) : F)^i.val := by
  simp only [sourceMixedWeight, mixingWeightsFold_eq, zero_add, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]

theorem sourceMixedWeight_dot (coinWeights : Fin 271 → F) (m : Fin 1024 → F) :
    (∑ i, sourceMixedWeight coinWeights i*m i) =
      ∑ j : Fin 271, coinWeights j*
        sourceMixHorner ((j.val+1 : ℕ) : F) (List.ofFn m) := by
  simp only [sourceMixedWeight_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceMixHorner_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem source_original_mixed_weight_dot (points : Fin 3 → Fin 10 → F)
    (kappa : F) (inactive : Finset (Fin 1024))
    (coinWeights : Fin 271 → F) (m : Fin 1024 → F) :
    (∑ i, sourceOriginalWeight points kappa inactive (sourceMixedWeight coinWeights) true i*m i) =
      kappa*(∑ j : Fin 271, coinWeights j*
        sourceMixHorner ((j.val+1 : ℕ) : F) (List.ofFn m)) +
      kappa^2*sourcePointFunctional (points 1) m +
      kappa^3*sourcePointFunctional (points 2) m + ∑ i ∈ inactive, m i := by
  rw [sourceOriginalWeight_dot]
  simp only [if_true, sourceMixedWeight_dot]

#print axioms mixingRowLoop_eq
#print axioms mixingWeightsFold_eq
#print axioms sourceMixedWeight_eq
#print axioms sourceMixedWeight_dot
#print axioms source_original_mixed_weight_dot
end AspisV8R17
