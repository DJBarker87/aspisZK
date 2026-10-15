import R1SamplerWordPass
import R0C.ModuloField
import AspisV8R19.R406SamplerWordDistribution

/-! A positional identity for the sampler's eight little-endian U32 words.
This is arithmetic/model plumbing only; it does not identify a Rust sampler
execution or probability law. -/

set_option autoImplicit false

namespace AspisR1.SamplerBlockRank

open AspisV8R19.SourceDuplexStep AspisV8R19.SamplerWords

/-- The reversed eight-word numeral is exactly the positional rank of all 32
state bytes, using the existing four-byte word-value lemma. -/
theorem word_numeral_eq_rank (s : State) :
    AspisR1.SamplerPass.numeral (2^32)
      ((List.ofFn fun j : Fin 8 => AspisV8R19.SamplerWords.word s j).reverse) =
      (R0C.ModuloField.blockRank s).val := by
  rw [R0C.ModuloField.blockRank_value]
  simp only [AspisR1.SamplerPass.numeral, List.ofFn_succ, List.ofFn_zero,
    List.reverse_cons, List.reverse_nil, List.append_nil, List.cons_append,
    List.nil_append, List.foldl_cons, List.foldl_nil,
    AspisV8R19.SamplerWords.word, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Fin.val_succ]
  -- The two expansions enumerate the same positions using different Fin
  -- constructors: the block-rank sum uses `Fin.mk`, while repeated `Fin.sum`
  -- expansion leaves nested `Fin.succ` indices. Normalize those constructors
  -- before asking ring to compare the 32 symbolic byte coefficients.
  simp only [Fin.succ]
  norm_num
  <;> ring

#print axioms word_numeral_eq_rank

end AspisR1.SamplerBlockRank
