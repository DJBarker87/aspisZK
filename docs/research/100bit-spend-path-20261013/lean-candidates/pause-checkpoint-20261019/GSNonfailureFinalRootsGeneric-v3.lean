import GSRejectingSamplerDecoderBank
import GSDecoderTapeReindex

set_option autoImplicit false

namespace AspisR1.GSNonfailureFinalRootsGeneric

open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSRejectingSamplerDecoderBank
open AspisR1.GSDecoderTapeReindex

variable {X K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

attribute [local irreducible] AspisR1.GSFixedInputDecoderFamily.run
  AspisR1.GSConcreteRootRecovery.initial
  AspisR1.GSConcreteRootRecovery.final

/-- A concrete output vector with no failed lane has successful results in
all five final positions. This is independent of any sampler or tape. -/
theorem final_roots_of_not_failed (out : Results K 5)
    (houtbad : ¬ AspisR1.GSFixedInputDecoderFamily.failed out) :
    ∃ roots : Fin 5 → List (List K),
      ∀ i : Fin 5, out.2 i = some (roots i) := by
  classical
  have hsuccess : ∀ i : Fin 5, ∃ r, out.2 i = some r := by
    intro i
    have hne : out.2 i ≠ none := by
      intro hn
      apply houtbad
      change ∃ j : Lane 5, Sum.elim out.1 out.2 j = none
      exact ⟨Sum.inr i, by simp only [Sum.elim_inr, hn]⟩
    cases hi : out.2 i with
    | none => exact False.elim (hne hi)
    | some r => exact ⟨r, rfl⟩
  choose roots hroots using hsuccess
  exact ⟨roots, hroots⟩

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
      have hsampleNone :
          AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun sample q inputs xs = none := by
        simp only [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs,
          Option.map_none]
      have hbad : AspisR1.GSRejectingSamplerDecoderBank.failed sample q inputs xs := by
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output sample q inputs xs).2
          (Or.inl hsampleNone)
      exact False.elim (hnofail hbad)
  | some raw =>
      let H := flatBank K (1025*112) (256*112) 149 raw
      let out := AspisR1.GSFixedInputDecoderFamily.run q 149 inputs H
      have houtbad : ¬ AspisR1.GSFixedInputDecoderFamily.failed out := by
        intro hbad
        apply hnofail
        have hsampleRun :
            AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun sample q inputs xs = some out := by
          simp only [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs,
            Option.map_some]
          rfl
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output sample q inputs xs).2
          (Or.inr ⟨out, hsampleRun, hbad⟩)
      obtain ⟨roots, hroots⟩ := final_roots_of_not_failed out houtbad
      have houtRun : out = AspisR1.GSFixedInputDecoderFamily.run q 149 inputs H := rfl
      exact ⟨raw, rfl, out, houtRun, roots, hroots⟩

#print axioms nonfailure_yields_all_final_roots

end AspisR1.GSNonfailureFinalRootsGeneric
