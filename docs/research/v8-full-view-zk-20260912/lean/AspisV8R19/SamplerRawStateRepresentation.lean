import AspisV8R19.SamplerWords

/-! Pure representation bridge for one 256-bit squeeze block.

This file only identifies the byte-array representation with eight little-endian
32-bit words.  It makes no claim about oracle freshness, sampling laws, or the
execution of the sampler.
-/
set_option autoImplicit false
namespace AspisV8R19.SamplerRawStateRepresentation

open DuplexFrames SourceDuplexStep SamplerWords

abbrev RawWord := Fin (2 ^ 32)

private def byteBlockEquiv : (Fin 4 → Byte) ≃
    (Byte × Byte) × (Byte × Byte) where
  toFun b := ((b 0, b 1), (b 2, b 3))
  invFun p := fun i =>
    match i.1 with
    | 0 => p.1.1
    | 1 => p.1.2
    | 2 => p.2.1
    | _ => p.2.2
  left_inv b := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
    rfl

private def littlePairEquiv : (Byte × Byte) ≃ Fin (256 * 256) :=
  (Equiv.prodComm Byte Byte).trans finProdFinEquiv

private def littleWordEquiv :
    ((Byte × Byte) × (Byte × Byte)) ≃ RawWord :=
  (littlePairEquiv.prodCongr littlePairEquiv).trans
    ((Equiv.prodComm _ _).trans
      (finProdFinEquiv.trans (finCongr (by norm_num))))

private def stateGridEquiv : (Fin 32 → Byte) ≃ (Fin 8 → Fin 4 → Byte) :=
  (Equiv.arrowCongr
      ((finProdFinEquiv : Fin 8 × Fin 4 ≃ Fin (8 * 4)).trans
        (finCongr (show 8 * 4 = 32 by norm_num)))
      (Equiv.refl Byte)).symm.trans
    (Equiv.curry (Fin 8) (Fin 4) Byte)

def stateRawEquiv : (Fin 32 → Byte) ≃ (Fin 8 → RawWord) :=
  stateGridEquiv.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin 8)) byteBlockEquiv).trans
      (Equiv.arrowCongr (Equiv.refl (Fin 8)) littleWordEquiv))

theorem stateRawEquiv_word (s : Fin 32 → Byte) (j : Fin 8) :
    ((stateRawEquiv s) j).val = SamplerWords.word s j := by
  have h1 : (⟨1 + 4 * j.val, by omega⟩ : Fin 32) =
      ⟨4 * j.val + 1, by omega⟩ := by
    apply Fin.ext
    change 1 + 4 * j.val = 4 * j.val + 1
    omega
  have h2 : (⟨2 + 4 * j.val, by omega⟩ : Fin 32) =
      ⟨4 * j.val + 2, by omega⟩ := by
    apply Fin.ext
    change 2 + 4 * j.val = 4 * j.val + 2
    omega
  have h3 : (⟨3 + 4 * j.val, by omega⟩ : Fin 32) =
      ⟨4 * j.val + 3, by omega⟩ := by
    apply Fin.ext
    change 3 + 4 * j.val = 4 * j.val + 3
    omega
  simp [stateRawEquiv, stateGridEquiv, littleWordEquiv, littlePairEquiv,
    byteBlockEquiv, SamplerWords.word, finProdFinEquiv, h1, h2, h3]
  ring

theorem stateRawEquiv_word_offsets (s : Fin 32 → Byte) :
    ∀ j : Fin 8, ((stateRawEquiv s) j).val =
      (s ⟨4 * j.val, by omega⟩).val +
      256 * (s ⟨4 * j.val + 1, by omega⟩).val +
      65536 * (s ⟨4 * j.val + 2, by omega⟩).val +
      16777216 * (s ⟨4 * j.val + 3, by omega⟩).val := by
  intro j
  exact stateRawEquiv_word s j

/-- A uniformly averaged 32-byte oracle answer is exactly the uniform average
over its eight little-endian 32-bit words.  This is only a representation
transport; freshness of a particular oracle read remains a separate premise. -/
theorem uniform_state_words (test : (Fin 8 → RawWord) → ℚ) :
    OracleResampling.mean (fun s : Fin 32 → Byte => test (stateRawEquiv s)) =
      OracleResampling.mean test := by
  exact OracleResampling.mean_equiv stateRawEquiv test

#print axioms stateRawEquiv_word
#print axioms stateRawEquiv_word_offsets
#print axioms uniform_state_words
end AspisV8R19.SamplerRawStateRepresentation
