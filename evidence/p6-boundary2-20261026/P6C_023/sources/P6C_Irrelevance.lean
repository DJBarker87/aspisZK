import P6C_Accepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Irrelevance
open Aeneas Aeneas.Std Result SdkC_Source

/-- Only the actual issued addresses need agree. Even successful calls at
unissued addresses may have different answers in the replacement. -/
theorem issued_only (hashv replacement : Parts → Result Digest) {A : Type}
    (code : Code A) (before : Log) (value : A)
    (accepted : (run hashv code before).1 = ok value)
    (agrees : ∀ q ∈ (run hashv code before).2, replacement q.parts = hashv q.parts) :
    run replacement code before = run hashv code before := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok a => exact ih a before accepted agrees
  | read parts k ih =>
    cases actual : hashv parts with
    | fail e => simp only [run,actual] at accepted; cases accepted
    | div => simp only [run,actual] at accepted; cases accepted
    | ok digest =>
      have member : (⟨parts,ok digest⟩ : Query) ∈ (run hashv (.read parts k) before).2 := by
        simp only [run,actual]
        obtain ⟨suffix,layout⟩ := prefix_preserved hashv (k digest) (before ++ [⟨parts,ok digest⟩])
        rw [layout]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
      have replacementCall : replacement parts = ok digest := (agrees _ member).trans actual
      simp only [run,actual,replacementCall] at accepted agrees ⊢
      exact ih digest _ accepted agrees

/-- Consequences may depend on the full output and full ordered log. This
transport does not merely preserve acceptance or final Merkle roots. -/
theorem conclusions {A : Type} (hashv replacement : Parts → Result Digest)
    (code : Code A) (value : A)
    (accepted : (run hashv code []).1 = ok value)
    (agrees : ∀ q ∈ (run hashv code []).2, replacement q.parts = hashv q.parts)
    (claim : Result A × Log → Prop) :
    claim (run replacement code []) ↔ claim (run hashv code []) := by
  rw [issued_only hashv replacement code [] value accepted agrees]

#print axioms issued_only
#print axioms conclusions
end AspisR1.P6C_Irrelevance
end
