import R1Z.PV_L2_F3CountedErasure
import R1Z.ProverCommitSourceDecoder

/-! Values and complete scalar-count arrays on the actual sequential decoder.
No concrete source-size recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3CountedArrays
open R1Z.ProverCommitSequentialFibres R1Z.PV_L2_F3CountedFibres
  R1Z.PV_L2_F3CountedErasure R1Z.ProverCommitSourceDecoder
attribute [local instance] Classical.propDecidable
variable {W A : Type} [Fintype W]

def split (A : Type) (L : Nat) : Values (A × Nat) L ≃ ((Fin L → A) × (Fin L → Nat)) :=
  (valuesEquiv (A × Nat) L).trans
    (Equiv.arrowProdEquivProdArrow (Fin L) (fun _ => A) (fun _ => Nat))

theorem split_values (L : Nat) (v : Values (A × Nat) L) :
    (split A L v).1 = valuesEquiv A L (strip L v) := by
  induction L with
  | zero => funext i; exact Fin.elim0 i
  | succ L ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih v.2) j

theorem split_counts (L : Nat) (v : Values (A × Nat) L) :
    (split A L v).2 = valuesEquiv Nat L (counts L v) := by
  induction L with
  | zero => funext i; exact Fin.elim0 i
  | succ L ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih v.2) j

def arrays (d : W → Option A) (n L r : Nat) (ws : Fin n → W) :
    Option ((Fin L → A) × (Fin L → Nat)) := (counted d n L r ws).map (split A L)

theorem arrays_erases (d : W → Option A) (n L r : Nat) (ws : Fin n → W) :
    (arrays d n L r ws).map Prod.fst = arrayDecode d n L r ws := by
  unfold arrays arrayDecode
  rw [← counted_erases d n L r ws]
  simp only [Option.map_map]
  congr 1
  funext v
  exact split_values L v

theorem arrays_equal_fibres (d : W → Option A) (c : Nat)
    (fibres : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c)
    (n L r : Nat) (a b : Fin L → A) (history : Fin L → Nat) :
    (Finset.univ.filter (fun ws : Fin n → W => arrays d n L r ws = some (a,history))).card =
      (Finset.univ.filter (fun ws : Fin n → W => arrays d n L r ws = some (b,history))).card := by
  have heq (out : (Fin L → A) × (Fin L → Nat)) :
      (Finset.univ.filter (fun ws : Fin n → W => arrays d n L r ws = some out)) =
        Finset.univ.filter (fun ws : Fin n → W => counted d n L r ws = some ((split A L).symm out)) := by
    ext ws
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,arrays]
    exact map_equiv_some (split A L) _ out
  rw [heq,heq]
  apply conditional_equal_fibres d c fibres
  apply (valuesEquiv Nat L).injective
  rw [← split_counts,← split_counts]
  simp only [Equiv.apply_symm_apply]

#print axioms split
#print axioms split_values
#print axioms split_counts
#print axioms arrays_erases
#print axioms arrays_equal_fibres
end R1Z.PV_L2_F3CountedArrays
