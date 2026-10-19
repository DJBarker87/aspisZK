import GSRejectingSamplerDecoderBank
import GSDecoderTapeReindex

set_option autoImplicit false

namespace AspisR1.GSNonfailureFinalRootsGeneric

open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSRejectingSamplerDecoderBank
open AspisR1.GSDecoderTapeReindex

variable {X K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- For any finite-tape sampler, nonfailure of the actual rejecting sampler
and fixed decoder bank yields a tape whose five final calls all return lists.
This generic helper leaves the concrete sampler and second-fold projection to
separate consumers. -/
theorem nonfailure_yields_all_final_roots
    (sample : X → Option (FlatTape K)) (q : Nat)
    (inputs : Inputs K 5) (xs : X)
    (hnofail : ¬ AspisR1.GSRejectingSamplerDecoderBank.failed sample q inputs xs) :
    ∃ raw : AspisR1.GSRejectingSamplerDecoderBank.FlatTape K,
      sample xs = some raw ∧
      ∃ out : Results K 5,
        out = AspisR1.GSFixedInputDecoderFamily.run q 149 inputs
          (flatBank K (1025*112) (256*112) 149 raw) ∧
        ∃ roots : Fin 5 → List (List K),
          ∀ i : Fin 5, out.2 i = some (roots i) := by
  classical
  cases hs : sample xs with
  | none =>
      have hbad : AspisR1.GSRejectingSamplerDecoderBank.failed sample q inputs xs := by
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output sample q inputs xs).2
          (Or.inl (by simp [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs]))
      exact False.elim (hnofail hbad)
  | some raw =>
      let H := flatBank K (1025*112) (256*112) 149 raw
      let out := AspisR1.GSFixedInputDecoderFamily.run q 149 inputs H
      have houtbad : ¬ AspisR1.GSFixedInputDecoderFamily.failed out := by
        intro hbad
        apply hnofail
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output sample q inputs xs).2
          (Or.inr ⟨out, by simp [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs, out, H], hbad⟩)
      have hsuccess : ∀ i : Fin 5, ∃ r,
          out.2 i = some r := by
        intro i
        have hne : out.2 i ≠ none := by
          intro hn
          apply houtbad
          exact ⟨Sum.inr i, by simp [AspisR1.GSFixedInputDecoderFamily.failed, hn]⟩
        cases hi : out.2 i with
        | none => exact False.elim (hne hi)
        | some r => exact ⟨r, rfl⟩
      choose roots hroots using hsuccess
      have houtRun : out = AspisR1.GSFixedInputDecoderFamily.run q 149 inputs H := rfl
      exact ⟨raw, rfl, out, houtRun, roots, hroots⟩

#print axioms nonfailure_yields_all_final_roots

end AspisR1.GSNonfailureFinalRootsGeneric
