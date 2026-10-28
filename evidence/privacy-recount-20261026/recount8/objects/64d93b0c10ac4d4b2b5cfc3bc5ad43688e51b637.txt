import R1Z.ProverCommitSequentialFibres

set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSequentialFibres
open R1Z.CommitReadsR1 R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable

def valuesEquiv (A : Type) : (n : Nat) → Values A n ≃ (Fin n → A)
  | 0 => {
      toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := fun v => by cases v; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => {
      toFun := fun v => Fin.cons v.1 (valuesEquiv A n v.2)
      invFun := fun f => (f 0, (valuesEquiv A n).symm (fun j => f j.succ))
      left_inv := fun v => by
        apply Prod.ext
        · rfl
        · exact (valuesEquiv A n).symm_apply_apply v.2
      right_inv := fun f => by
        funext i
        refine Fin.cases rfl (fun j => ?_) i
        exact congrFun ((valuesEquiv A n).apply_symm_apply (fun j => f j.succ)) j }

variable {W A : Type} [Fintype W]

def arrayDecode (d : W → Option A) (n L r : Nat) (ws : Fin n → W) : Option (Fin L → A) :=
  (decodeWords d n L r ws).map (valuesEquiv A L)

theorem array_equal_fibres (d : W → Option A) (c₀ c₁ : Nat)
    (hz : (Finset.univ.filter (fun w => d w = none)).card = c₀)
    (ha : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c₁) (n L r : Nat) (out : Fin L → A) :
    (Finset.univ.filter (fun ws : Fin n → W => arrayDecode d n L r ws = some out)).card =
      fibreSize (Fintype.card W) c₀ c₁ n L r := by
  have eq : (Finset.univ.filter (fun ws : Fin n → W => arrayDecode d n L r ws = some out)) =
      (Finset.univ.filter (fun ws => decodeWords d n L r ws = some ((valuesEquiv A L).symm out))) := by
    ext ws
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, arrayDecode]
    cases h : decodeWords d n L r ws with
    | none => simp
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      exact (valuesEquiv A L).apply_eq_iff_eq_symm_apply
  rw [eq]
  exact sequential_equal_fibres d c₀ c₁ hz ha n L r _

def pairDecode (d : W → Option A) (n₁ n₂ L₁ L₂ : Nat)
    (ws : (Fin n₁ → W) × (Fin n₂ → W)) : Option ((Fin L₁ → A) × (Fin L₂ → A)) := do
  let a ← arrayDecode d n₁ L₁ 16 ws.1
  let b ← arrayDecode d n₂ L₂ 16 ws.2
  pure (a,b)

theorem pair_equal_fibres (d : W → Option A) (c₀ c₁ : Nat)
    (hz : (Finset.univ.filter (fun w => d w = none)).card = c₀)
    (ha : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c₁) (n₁ n₂ L₁ L₂ : Nat) (out : (Fin L₁ → A) × (Fin L₂ → A)) :
    (Finset.univ.filter (fun ws => pairDecode d n₁ n₂ L₁ L₂ ws = some out)).card =
      fibreSize (Fintype.card W) c₀ c₁ n₁ L₁ 16 * fibreSize (Fintype.card W) c₀ c₁ n₂ L₂ 16 := by
  have eq : (Finset.univ.filter (fun ws => pairDecode d n₁ n₂ L₁ L₂ ws = some out)) =
      (Finset.univ.filter (fun ws => arrayDecode d n₁ L₁ 16 ws = some out.1)) ×ˢ
      (Finset.univ.filter (fun ws => arrayDecode d n₂ L₂ 16 ws = some out.2)) := by
    ext ws
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    cases h₁ : arrayDecode d n₁ L₁ 16 ws.1 <;>
      cases h₂ : arrayDecode d n₂ L₂ 16 ws.2 <;> simp [pairDecode, h₁, h₂, Prod.ext_iff]
  rw [eq, Finset.card_product, array_equal_fibres d c₀ c₁ hz ha, array_equal_fibres d c₀ c₁ hz ha]

#print axioms valuesEquiv
#print axioms array_equal_fibres
#print axioms pair_equal_fibres
end R1Z.ProverCommitSequentialFibres
