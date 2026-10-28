import R1Z.ProverCommitQuotientLaw

/-! A lossless field-coordinate carrier for the source's five sampled arrays.
The ordering of the Rust caller's cells is a separate execution identity. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceCarrier
open R0P R0Z.JointView R0Z.MaskLayout R1Z.ProverCommitTapeCompletion
attribute [local instance] Classical.propDecidable
abbrev FreeRow := {r : Fin 1024 // r ≠ 0 ∧ ¬ CopyActiveRow r}
instance : Fintype FreeRow := Fintype.ofFinite _
variable {K : Type} [Field K] {F : Subfield K}

abbrev Samples (K : Type) [Field K] (F : Subfield K) :=
  (EligibleCell → F) × ((Fin 10 × Fin 1024 → F) ×
    ((Fin 1024 × Fin 4 → F) × ((FreeRow × Fin 4 → F) × (Fin 1024 × Fin 4 → F))))

def toTape (s : Samples K F) : Tape K F :=
  ((fun c => match c with
    | .inl cr => s.2.1 cr
    | .inr (lane,row,limb) =>
      if lane = 0 then s.2.2.1 (row,limb)
      else if lane = 1 then
        if hr : row ≠ 0 ∧ ¬ CopyActiveRow row then s.2.2.2.1 (⟨row,hr⟩,limb) else 0
      else s.2.2.2.2 (row,limb)), s.1)

def fromQuotient (s : SourceTape K F) : Samples K F :=
  (s.2, (fun cr => s.1 ⟨.inl cr, by simp only [Ignored, not_false_eq_true]⟩),
    (fun rl => s.1 ⟨.inr (0,rl.1,rl.2), by simp [Ignored]⟩),
    (fun rl => s.1 ⟨.inr (1,rl.1.1,rl.2), by
      intro bad
      exact bad.2.elim rl.1.2.1 rl.1.2.2⟩),
    (fun rl => s.1 ⟨.inr (2,rl.1,rl.2), by simp [Ignored]⟩))

theorem from_to (s : Samples K F) : fromQuotient (project (toTape s)) = s := by
  rcases s with ⟨noise,masks,g,h1,d⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext rl; simp only [fromQuotient, project, toTape, ite_true]
  apply Prod.ext
  · funext rl
    simp only [fromQuotient, project, toTape, show (1 : Fin 3) ≠ 0 by decide,
      if_false, ite_true]
    rw [dif_pos rl.1.2]
  · funext rl
    simp only [fromQuotient, project, toTape, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, if_false]

theorem to_from (s : SourceTape K F) : project (toTape (fromQuotient s)) = s := by
  apply Prod.ext
  · funext c
    rcases c with ⟨c,hc⟩
    cases c with
    | inl cr => rfl
    | inr coord =>
      rcases coord with ⟨lane,row,limb⟩
      have hr : lane = 1 → row ≠ 0 ∧ ¬ CopyActiveRow row := by
        intro hl
        exact ⟨fun h0 => hc ⟨hl, Or.inl h0⟩, fun ha => hc ⟨hl, Or.inr ha⟩⟩
      have cases : lane = 0 ∨ lane = 1 ∨ lane = 2 := by
        have := lane.isLt
        omega
      rcases cases with hl | hl | hl
      · subst lane; rfl
      · subst lane
        simp only [project, toTape, fromQuotient, show (1 : Fin 3) ≠ 0 by decide,
          if_false, ite_true, dif_pos (hr rfl)]
      · subst lane; rfl
  · rfl

def sourceCarrierEquiv : Samples K F ≃ SourceTape K F where
  toFun s := project (toTape s)
  invFun := fromQuotient
  left_inv := from_to
  right_inv := to_from

/-- Mapping all five actual arrays into the quotient loses no field sample. -/
theorem source_fibre_card {Input : Type} [Fintype Input] [Fintype K]
    (decode : Input → Option (Samples K F)) (s : SourceTape K F) :
    (Finset.univ.filter (fun i => (decode i).map sourceCarrierEquiv = some s)).card =
      (Finset.univ.filter (fun i => decode i = some (fromQuotient s))).card := by
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hi : decode i with
  | none => simp
  | some a => simp only [Option.map_some, Option.some.injEq]
              exact sourceCarrierEquiv.apply_eq_iff_eq_symm_apply

#print axioms from_to
#print axioms to_from
#print axioms sourceCarrierEquiv
#print axioms source_fibre_card
end R1Z.ProverCommitSourceCarrier
