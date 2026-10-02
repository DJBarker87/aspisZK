import AspisV8R19.SamplerWords
import AspisV8R19.OracleResampling
import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite bijections for source little-endian words and their 18-bit
mask. This does not supply independent answers for the shared source oracle. -/
set_option autoImplicit false
namespace AspisV8R19.R406SamplerWordDistribution
open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
noncomputable section

def index (j : Fin 8) (k : Fin 4) : Fin 32 := finProdFinEquiv (j,k)

def byteBlockEquiv : State ≃ (Fin 8 → Fin 4 → Byte) where
  toFun block j k := block (index j k)
  invFun f i := let p : Fin 8 × Fin 4 := finProdFinEquiv.symm i; f p.1 p.2
  left_inv block := by
    funext i
    change block (finProdFinEquiv (finProdFinEquiv.symm i)) = block i
    exact congrArg block (finProdFinEquiv.apply_symm_apply i)
  right_inv f := by
    funext j k
    exact congrArg (fun p : Fin 8 × Fin 4 => f p.1 p.2)
      (finProdFinEquiv.symm_apply_apply (j,k))

def byteWordEquiv : (Fin 4 → Byte) ≃ Fin (2^32) := finFunctionFinEquiv

def blockWordEquiv : State ≃ (Fin 8 → Fin (2^32)) :=
  byteBlockEquiv.trans (Equiv.piCongrRight (fun _ => byteWordEquiv))

def splitWordEquiv : Fin (2^32) ≃ (Fin (2^14) × Fin (2^18)) :=
  (finProdFinEquiv (m := 2^14) (n := 2^18)).symm

def distribute : (Fin 8 → Fin (2^14) × Fin (2^18)) ≃
    ((Fin 8 → Fin (2^14)) × (Fin 8 → Fin (2^18))) where
  toFun f := (fun j => (f j).1, fun j => (f j).2)
  invFun p j := (p.1 j,p.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

def splitBlockEquiv : State ≃
    ((Fin 8 → Fin (2^14)) × (Fin 8 → Fin (2^18))) :=
  (blockWordEquiv.trans (Equiv.piCongrRight (fun _ => splitWordEquiv))).trans distribute

theorem word_value (block : State) (j : Fin 8) :
    (blockWordEquiv block j).val = SamplerWords.word block j := by
  change (finFunctionFinEquiv (fun k => block (index j k))).val = _
  rw [finFunctionFinEquiv_apply]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    Nat.mul_one, Fin.sum_univ_zero, Nat.add_zero]
  have ix (k : Fin 4) : index j k = ⟨4*j.val+k.val,by omega⟩ := by
    apply Fin.ext
    change k.val + 4*j.val = 4*j.val + k.val
    omega
  simp only [ix]
  change (block ⟨4*j.val,by omega⟩).val +
    ((block ⟨4*j.val+1,by omega⟩).val * 256 +
    ((block ⟨4*j.val+2,by omega⟩).val * 65536 +
    (block ⟨4*j.val+3,by omega⟩).val * 16777216)) = _
  unfold SamplerWords.word
  ac_rfl

theorem masked_value (block : State) (j : Fin 8) :
    ((splitBlockEquiv block).2 j).val = masked 18 (SamplerWords.word block j) := by
  change (blockWordEquiv block j).val % 2^18 = _
  rw [word_value,masked_eq_mod]

theorem words_value (block : State) :
    words 18 block = List.ofFn (fun j => ((splitBlockEquiv block).2 j).val) := by
  unfold words
  congr 1
  funext j
  exact (masked_value block j).symm

theorem uniform_candidates (test : List Nat → ℚ) :
    mean (fun block : State => test (words 18 block)) =
      mean (fun candidates : Fin 8 → Fin (2^18) =>
        test (List.ofFn (fun j => (candidates j).val))) := by
  simp_rw [words_value]
  rw [mean_equiv splitBlockEquiv
    (fun p => test (List.ofFn (fun j => (p.2 j).val)))]
  rw [mean_prod (fun (_ : Fin 8 → Fin (2^14)) (candidates : Fin 8 → Fin (2^18)) =>
    test (List.ofFn (fun j => (candidates j).val)))]
  exact mean_const _

#print axioms word_value
#print axioms masked_value
#print axioms words_value
#print axioms uniform_candidates
end
end AspisV8R19.R406SamplerWordDistribution
