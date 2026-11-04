import R1Z.ProverCommitWordCarrier

/-! Exact successful fibres for a consuming rejection stream. Successful
limbs consume only through their accepted word; no 16-word padding per limb. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSequentialFibres
open R1Z.CommitReadsR1 R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable

def step {B T A V : Type} (d : B → Option A) (more : T → Option (A × V))
    (less : T → Option V) (bt : B × T) : Option (A × V) :=
  match d bt.1 with
  | none => more bt.2
  | some a => (less bt.2).map (fun v => (a,v))

theorem step_fibre_card {B T A V : Type} [Fintype B] [Fintype T]
    (d : B → Option A) (more : T → Option (A × V)) (less : T → Option V) (out : A × V) :
    (Finset.univ.filter (fun bt => step d more less bt = some out)).card =
      (Finset.univ.filter (fun b => d b = none)).card *
        (Finset.univ.filter (fun t => more t = some out)).card +
      (Finset.univ.filter (fun b => d b = some out.1)).card *
        (Finset.univ.filter (fun t => less t = some out.2)).card := by
  have eq : (Finset.univ.filter (fun bt => step d more less bt = some out)) =
      ((Finset.univ.filter (fun b => d b = none)) ×ˢ
        (Finset.univ.filter (fun t => more t = some out))) ∪
      ((Finset.univ.filter (fun b => d b = some out.1)) ×ˢ
        (Finset.univ.filter (fun t => less t = some out.2))) := by
    ext bt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    rcases bt with ⟨b,t⟩
    cases hd : d b with
    | none => simp [step, hd]
    | some a =>
      cases hl : less t with
      | none => simp [step, hd, hl]
      | some v => simp [step, hd, hl, Prod.ext_iff]
  rw [eq, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product]
  apply Finset.disjoint_left.mpr
  intro bt h₁ h₂
  have hnone := (Finset.mem_filter.mp (Finset.mem_product.mp h₁).1).2
  have hsome := (Finset.mem_filter.mp (Finset.mem_product.mp h₂).1).2
  rw [hnone] at hsome
  contradiction

def Values (A : Type) : Nat → Type
  | 0 => PUnit
  | n+1 => A × Values A n

variable {W A : Type} [Fintype W]

def decodeWords (d : W → Option A) : (n L r : Nat) → (Fin n → W) → Option (Values A L)
  | 0, 0, _, _ => some PUnit.unit
  | 0, _+1, _, _ => none
  | _+1, 0, _, _ => some PUnit.unit
  | _+1, _+1, 0, _ => none
  | n+1, L+1, r+1, ws =>
    step d (decodeWords d n (L+1) r) (decodeWords d n L 16)
      (ws 0, fun j => ws j.succ)

def wordTailEquiv (W : Type) (n : Nat) : (Fin (n+1) → W) ≃ W × (Fin n → W) where
  toFun ws := (ws 0, fun j => ws j.succ)
  invFun bt := Fin.cons bt.1 bt.2
  left_inv ws := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv bt := rfl

def consumingFibreEquiv (d : W → Option A) (n L r : Nat) (out : Values A (L+1)) :
    {ws : Fin (n+1) → W // decodeWords d (n+1) (L+1) (r+1) ws = some out} ≃
    {bt : W × (Fin n → W) //
      step d (decodeWords d n (L+1) r) (decodeWords d n L 16) bt = some out} where
  toFun ws := ⟨wordTailEquiv W n ws.1, ws.2⟩
  invFun bt := ⟨(wordTailEquiv W n).symm bt.1, bt.2⟩
  left_inv ws := Subtype.ext ((wordTailEquiv W n).left_inv ws.1)
  right_inv bt := Subtype.ext ((wordTailEquiv W n).right_inv bt.1)

def fibreSize (q c₀ c₁ : Nat) : Nat → Nat → Nat → Nat
  | 0, 0, _ => 1
  | 0, _+1, _ => 0
  | n+1, 0, _ => q^(n+1)
  | _+1, _+1, 0 => 0
  | n+1, L+1, r+1 => c₀ * fibreSize q c₀ c₁ n (L+1) r + c₁ * fibreSize q c₀ c₁ n L 16

/-- Variable-consumption rejection has equal successful fibres. -/
theorem sequential_equal_fibres (d : W → Option A) (c₀ c₁ : Nat)
    (hz : (Finset.univ.filter (fun w => d w = none)).card = c₀)
    (ha : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c₁)
    (n L r : Nat) (out : Values A L) :
    (Finset.univ.filter (fun ws : Fin n → W => decodeWords d n L r ws = some out)).card =
      fibreSize (Fintype.card W) c₀ c₁ n L r := by
  induction n generalizing L r with
  | zero =>
    cases L with
    | zero => cases out; simp [decodeWords, fibreSize]
    | succ L => simp [decodeWords, fibreSize]
  | succ n ih =>
    cases L with
    | zero => cases out; simp [decodeWords, fibreSize, Fintype.card_fun, Fintype.card_fin]
    | succ L =>
      cases r with
      | zero => simp [decodeWords, fibreSize]
      | succ r =>
        have hc := Fintype.card_congr (consumingFibreEquiv d n L r out)
        simp only [Fintype.card_subtype] at hc
        have hs := @step_fibre_card W (Fin n → W) A (Values A L) inferInstance inferInstance d
          (decodeWords d n (L+1) r) (decodeWords d n L 16) out
        have he := congrArg₂ Nat.add (congrArg₂ Nat.mul hz (ih (L+1) r out))
          (congrArg₂ Nat.mul (ha out.1) (ih L 16 out.2))
        have he' :
            (Finset.univ.filter (fun b : W => d b = none)).card *
              (Finset.univ.filter (fun t : Fin n → W => decodeWords d n (L+1) r t = some out)).card +
            (Finset.univ.filter (fun b : W => d b = some out.1)).card *
              (Finset.univ.filter (fun t : Fin n → W => decodeWords d n L 16 t = some out.2)).card =
            fibreSize (Fintype.card W) c₀ c₁ (n+1) (L+1) (r+1) := by
          convert he using 4 <;> first
          | rfl
          | (congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
          | simp only [fibreSize]
        calc
          _ = (Finset.univ.filter (fun bt : W × (Fin n → W) =>
              step d (decodeWords d n (L+1) r) (decodeWords d n L 16) bt = some out)).card := by
                convert hc using 1 <;> congr 1 <;> ext z <;>
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          _ = (Finset.univ.filter (fun b : W => d b = none)).card *
              (Finset.univ.filter (fun t : Fin n → W => decodeWords d n (L+1) r t = some out)).card +
            (Finset.univ.filter (fun b : W => d b = some out.1)).card *
              (Finset.univ.filter (fun t : Fin n → W => decodeWords d n L 16 t = some out.2)).card := by
                convert hs using 4 <;> congr 1 <;> ext z <;>
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          _ = _ := he'

#print axioms step_fibre_card
#print axioms wordTailEquiv
#print axioms consumingFibreEquiv
#print axioms sequential_equal_fibres
end R1Z.ProverCommitSequentialFibres
