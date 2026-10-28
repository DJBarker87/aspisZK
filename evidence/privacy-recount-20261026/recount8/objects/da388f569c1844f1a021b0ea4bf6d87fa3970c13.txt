import R1Z.PV_RunJoin_WorldDecode33
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Factor
open PV_W_Threading PV_RunJoin_WorldDecode33
variable {W C A V : Type}

/-- The precise missing obligation on reachable runs. It compares the entire
observation, including failure and divergence prefixes. -/
def Fibres (reachable : Run W C Aeneas.Std.Error A → Prop)
    (observe : Run W C Aeneas.Std.Error A → V) : Prop :=
  ∀ l r, reachable l → reachable r → returned l = returned r → observe l = observe r

/-- A Result decoder exists exactly when the complete observation factors
through that Result on the admitted runs. This theorem supplies no native
instance of the right-hand side. -/
theorem exists_iff [Nonempty V]
    (reachable : Run W C Aeneas.Std.Error A → Prop)
    (observe : Run W C Aeneas.Std.Error A → V) :
    (∃ decode : Aeneas.Std.Result (A × W) → V,
      ∀ r, reachable r → decode (returned r) = observe r) ↔ Fibres reachable observe := by
  classical
  constructor
  · rintro ⟨decode,law⟩ l r hl hr same
    rw [← law l hl,← law r hr,same]
  · intro fibres
    let decode := fun out : Aeneas.Std.Result (A × W) =>
      if h : ∃ r, reachable r ∧ returned r = out then observe (Classical.choose h)
      else Classical.choice (inferInstance : Nonempty V)
    refine ⟨decode,?_⟩
    intro r hr
    have h : ∃ s, reachable s ∧ returned s = returned r := ⟨r,hr,rfl⟩
    dsimp only [decode]
    rw [dif_pos h]
    exact fibres _ r (Classical.choose_spec h).1 hr (Classical.choose_spec h).2

theorem pair_iff {U : Type}
    (reachable : Run W C Aeneas.Std.Error A → Prop)
    (disclosed : Run W C Aeneas.Std.Error A → V)
    (oracle : Run W C Aeneas.Std.Error A → U) :
    Fibres reachable (fun r => (disclosed r,oracle r)) ↔
      Fibres reachable disclosed ∧ Fibres reachable oracle := by
  constructor
  · intro h
    exact ⟨fun l r hl hr same => congrArg Prod.fst (h l r hl hr same),
      fun l r hl hr same => congrArg Prod.snd (h l r hl hr same)⟩
  · rintro ⟨hd,ho⟩ l r hl hr same
    exact Prod.ext (hd l r hl hr same) (ho l r hl hr same)

#print axioms exists_iff
#print axioms pair_iff
end R1Z.PV_RJDec_Factor
