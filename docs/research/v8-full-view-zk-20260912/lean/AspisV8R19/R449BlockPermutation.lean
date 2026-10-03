import AspisV8R19.R445InitialBlockRejectionLaw
import AspisV8R19.R446RejectionListExecution

set_option autoImplicit false

namespace AspisV8R19.R449BlockPermutation

open AspisV8R19.R442RejectionAlphabet
open AspisV8R19.R443BoundedRejectionMass
open AspisV8R19.R445InitialBlockRejectionLaw
open AspisV8R19.R421UniformMasked31Block

noncomputable section

/-- Apply one accepted-word permutation while preserving the rejection sentinel. -/
def wordPerm {p : Nat} (σ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  (alphabetEquiv p).trans ((Equiv.optionCongr σ).trans (alphabetEquiv p).symm)

theorem alphabetDecode_wordPerm {p : Nat} (σ : Equiv.Perm (Fin p))
    (w : Fin (p + 1)) :
    alphabetDecode p (wordPerm σ w) = Option.map σ (alphabetDecode p w) := by
  change (alphabetEquiv p) ((alphabetEquiv p).symm
    ((Equiv.optionCongr σ) ((alphabetEquiv p) w))) =
      Option.map σ ((alphabetEquiv p) w)
  rw [(alphabetEquiv p).apply_symm_apply]
  rfl

theorem wordPerm_fixes_sentinel {p : Nat} (σ : Equiv.Perm (Fin p)) :
    wordPerm σ (Fin.last p) = Fin.last p := by
  apply Fin.ext
  have hge : p ≤ (wordPerm σ (Fin.last p)).val := by
    simpa [alphabetDecode] using (alphabetDecode_wordPerm σ (Fin.last p))
  have hval : (wordPerm σ (Fin.last p)).val = p := by
    omega
  simpa using hval

/-- The bounded rejection fold commutes with a permutation of accepted values. -/
theorem run_map {p : Nat} (σ : Equiv.Perm (Fin p)) :
    ∀ (n : Nat) (t : Tape p n),
      run n (fun i => Option.map σ (t i)) = Option.map σ (run n t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
      intro t
      cases h : t 0 with
      | none =>
          simpa [run, h] using ih (fun i => t i.succ)
      | some a =>
          simp [run, h]

/-- Reindex a source block by permuting each of its eight accepted-word slots. -/
def blockPerm (σ : Equiv.Perm (Fin modulus)) :
    SourceDuplexStep.State ≃ SourceDuplexStep.State :=
  (splitBlock31Equiv).trans
    ((Equiv.prodCongr (Equiv.refl _)
      (Equiv.piCongrRight (fun _ => wordPerm (p := modulus) σ))).trans
      splitBlock31Equiv.symm)

theorem splitBlock31_blockPerm (σ : Equiv.Perm (Fin modulus))
    (block : SourceDuplexStep.State) :
    splitBlock31Equiv (blockPerm σ block) =
      Equiv.prodCongr (Equiv.refl _)
        (Equiv.piCongrRight (fun _ => wordPerm (p := modulus) σ))
        (splitBlock31Equiv block) := by
  simp [blockPerm, Equiv.trans_apply]

theorem decodeTape_wordPerm {p n : Nat} (σ : Equiv.Perm (Fin p))
    (words : Fin n → Fin (p + 1)) :
    decodeTapeEquiv p n (fun i => wordPerm σ (words i)) =
      fun i => Option.map σ (decodeTapeEquiv p n words i) := by
  funext i
  change alphabetDecode p (wordPerm σ (words i)) =
    Option.map σ (alphabetDecode p (words i))
  exact alphabetDecode_wordPerm σ (words i)

/-- The actual first-accepted initial block result is equivariant under the
accepted-value permutation induced on all eight source words. -/
theorem initialBlockResult_blockPerm (σ : Equiv.Perm (Fin modulus))
    (block : SourceDuplexStep.State) :
    initialBlockResult (blockPerm σ block) =
      Option.map σ (initialBlockResult block) := by
  unfold initialBlockResult
  rw [splitBlock31_blockPerm]
  change run 8 (decodeTapeEquiv modulus 8
    (fun i => wordPerm σ ((splitBlock31Equiv block).2 i))) =
    Option.map σ (run 8 (decodeTapeEquiv modulus 8 ((splitBlock31Equiv block).2)))
  rw [decodeTape_wordPerm, run_map]

#print axioms alphabetDecode_wordPerm
#print axioms wordPerm_fixes_sentinel
#print axioms run_map
#print axioms splitBlock31_blockPerm
#print axioms decodeTape_wordPerm
#print axioms initialBlockResult_blockPerm

end

end AspisV8R19.R449BlockPermutation
