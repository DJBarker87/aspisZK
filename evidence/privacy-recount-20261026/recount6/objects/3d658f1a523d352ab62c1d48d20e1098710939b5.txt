import R1Z.ProverCommitSourceCounts

/-! A symbolic successful input prevents vacuous all-failure fibre laws. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSequentialFibres
attribute [local instance] Classical.propDecidable

theorem constant_success {W A : Type} (d : W → Option A) (w : W) (a : A)
    (hw : d w = some a) (n L r : Nat) (hL : L ≤ n) (hr : 0 < r) :
    ∃ out, decodeWords d n L r (fun _ => w) = some out := by
  induction n generalizing L r with
  | zero =>
    have h : L = 0 := by omega
    subst L
    exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    cases L with
    | zero => exact ⟨PUnit.unit, rfl⟩
    | succ L =>
      obtain ⟨out, hout⟩ := ih L 16 (by omega) (by omega)
      cases r with
      | zero => omega
      | succ r =>
        exact ⟨(a,out), by simp only [decodeWords, step, hw, hout, Option.map_some] <;> rfl⟩

#print axioms constant_success
end R1Z.ProverCommitSequentialFibres

namespace R1Z.ProverCommitSourceDecoder
open R1Z.ProverCommitSequentialFibres R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] L₁ L₂ arrayCarrierEquiv sourceBase

theorem decoder_has_success : ∃ (e : Inputs) (s : R1Z.ProverCommitTapeCompletion.SourceTape K (sourceBase (K := K))),
    quotientDecoder e = some s := by
  let a := (baseEquiv (K := K)) (0 : Fin AspisCircleGroupOrder.P)
  have ha : accepted (K := K) (0 : R1Z.CommitReadsR1.Word) = some a := by
    simp only [accepted, Fin.val_zero, Nat.zero_mod, dif_pos (NeZero.pos AspisCircleGroupOrder.P)]
    rfl
  have hL₁ : L₁ ≤ E₁*8 := by unfold E₁; omega
  have hL₂ : L₂ ≤ E₂*8 := by unfold E₂; omega
  obtain ⟨v₁,h₁⟩ := constant_success (accepted (K := K)) 0 a ha (E₁*8) L₁ 16 hL₁ (by omega)
  obtain ⟨v₂,h₂⟩ := constant_success (accepted (K := K)) 0 a ha (E₂*8) L₂ 16 hL₂ (by omega)
  let ws := ((fun _ : Fin (E₁*8) => (0 : R1Z.CommitReadsR1.Word)),
    (fun _ : Fin (E₂*8) => (0 : R1Z.CommitReadsR1.Word)))
  refine ⟨inputEquiv.symm ws, arrayCarrierEquiv ((valuesEquiv _ L₁) v₁, (valuesEquiv _ L₂) v₂), ?_⟩
  simp [quotientDecoder, pairDecode, arrayDecode, ws, h₁, h₂]

#print axioms decoder_has_success
end R1Z.ProverCommitSourceDecoder
