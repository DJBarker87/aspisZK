import R1Z.SideChannelEntropy

/-! A source-shaped rejection-cell permutation. Each u32 consists of one
high bit and a 31-bit candidate. Candidate P rejects, every smaller value
is a canonical M31. Permuting canonical values fixes the rejected cell,
its high bit, and hence scalar/refill/partial-tower control for a common
word schedule. This does not assume successful masks are resampled. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Words
attribute [local instance] Classical.propDecidable
abbrev Candidate := Fin (2147483647 + 1)

def cellEquiv : Candidate ≃ Option (Fin 2147483647) where
  toFun c := if h : c.val < 2147483647 then some ⟨c.val,h⟩ else none
  invFun c := match c with
    | none => ⟨2147483647, by omega⟩
    | some c => ⟨c.val, by have := c.isLt; omega⟩
  left_inv c := by
    dsimp only
    split_ifs with hc
    · rfl
    · apply Fin.ext; have := c.isLt; dsimp only; omega
  right_inv c := by
    cases c with
    | none => simp only [dif_neg (by omega : ¬ (2147483647 < 2147483647))]
    | some c => simp only [dif_pos c.isLt]

/-- Keep the high bit and reject marker; permute only canonical values. -/
def permute (e : Fin 2147483647 ≃ Fin 2147483647) : Candidate ≃ Candidate :=
  cellEquiv.trans ((Equiv.optionCongr e).trans cellEquiv.symm)

def accepts (c : Candidate) : Prop := c.val < 2147483647

theorem accepts_permute (e : Fin 2147483647 ≃ Fin 2147483647) (c : Candidate) :
    accepts (permute e c) ↔ accepts c := by
  change (permute e c).val < 2147483647 ↔ c.val < 2147483647
  unfold permute
  by_cases hc : c.val < 2147483647
  · simp only [Equiv.trans_apply, cellEquiv, dif_pos hc, Equiv.optionCongr_apply,
      Option.map_some, Equiv.symm_mk, Equiv.coe_fn_mk]
    exact iff_of_true (e ⟨c.val,hc⟩).isLt hc
  · simp only [Equiv.trans_apply, cellEquiv, dif_neg hc, Equiv.optionCongr_apply,
      Option.map_none, Equiv.symm_mk, Equiv.coe_fn_mk]
    omega

/-- Full rejection prefix, including the first accepted word's position. -/
def control : Nat → (Nat → Candidate) → Nat → List Bool
  | 0, _, _ => []
  | n+1, words, cursor =>
    let accept := decide (accepts (words cursor))
    accept :: if accept then [] else control n words (cursor+1)

theorem control_permute (e : Fin 2147483647 ≃ Fin 2147483647)
    (n : Nat) (words : Nat → Candidate) (cursor : Nat) :
    control n (fun i => permute e (words i)) cursor = control n words cursor := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
    simp only [control, propext (accepts_permute e (words cursor)), ih]

#print axioms cellEquiv
#print axioms accepts_permute
#print axioms control_permute
end R1Z.PV_L2_F3Words
