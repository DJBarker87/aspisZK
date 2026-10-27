import R1Z.GamesR1PBin

/-! A lossless quotient/completion of the actual model tape. Completion entropy
is explicit; this does not manufacture entropy from deterministic zero fill. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView R0Z.MaskLayout R0P
attribute [local instance] Classical.propDecidable

/-- Exactly the raw H1 coordinates ignored by h1Padding. -/
def Ignored : AffCoordinate → Prop
  | .inl _ => False
  | .inr (lane, row, _) => lane = 1 ∧ (row = 0 ∨ CopyActiveRow row)

abbrev Visible := {c : AffCoordinate // ¬ Ignored c}
abbrev Hidden := {c : AffCoordinate // Ignored c}
instance : Fintype Visible := Fintype.ofFinite Visible
instance : Fintype Hidden := Fintype.ofFinite Hidden
abbrev SourceTape (K : Type) [Field K] (F : Subfield K) :=
  (Visible → F) × EligibleNoise K F
abbrev Padding (K : Type) [Field K] (F : Subfield K) := Hidden → F

instance {K : Type} [Field K] [Fintype K] (F : Subfield K) :
    Fintype (SourceTape K F) := Fintype.ofFinite _
instance {K : Type} [Field K] [Fintype K] (F : Subfield K) :
    Fintype (Padding K F) := Fintype.ofFinite _

variable {K : Type} [Field K] {F : Subfield K}

def project (t : Tape K F) : SourceTape K F :=
  ((fun c => t.1 c.1), t.2)

def padding (t : Tape K F) : Padding K F := fun c => t.1 c.1

def complete (s : SourceTape K F) (h : Padding K F) : Tape K F :=
  ((fun c => if hc : Ignored c then h ⟨c, hc⟩ else s.1 ⟨c, hc⟩), s.2)

theorem project_complete (s : SourceTape K F) (h : Padding K F) :
    project (complete s h) = s := by
  rcases s with ⟨v, e⟩
  simp only [project, complete, Prod.mk.injEq]
  constructor
  · funext c
    exact dif_neg c.2
  · trivial

theorem padding_complete (s : SourceTape K F) (h : Padding K F) :
    padding (complete s h) = h := by
  funext c
  exact dif_pos c.2

theorem complete_project (t : Tape K F) :
    complete (project t) (padding t) = t := by
  apply Prod.ext
  · funext c
    dsimp [complete, project, padding]
    split <;> rfl
  · rfl

/-- Product completion is a bijection, hence every full tape has one fibre.
The padding coordinate is retained randomness, not a fixed value. -/
def completionEquiv : (SourceTape K F × Padding K F) ≃ Tape K F where
  toFun s := complete s.1 s.2
  invFun t := (project t, padding t)
  left_inv s := by
    apply Prod.ext
    · exact project_complete _ _
    · exact padding_complete _ _
  right_inv := complete_project

theorem completion_equal_fibres [Fintype K] (t : Tape K F) :
    (Finset.univ.filter (fun s : SourceTape K F × Padding K F =>
      complete s.1 s.2 = t)).card = 1 := by
  classical
  have h : (Finset.univ.filter (fun s : SourceTape K F × Padding K F =>
      complete s.1 s.2 = t)) = {completionEquiv.symm t} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact completionEquiv.apply_eq_iff_eq_symm_apply
  rw [h, Finset.card_singleton]

/-- Each quotient fibre is precisely one copy of the ignored-coordinate tape. -/
def quotientFibreEquiv (s : SourceTape K F) :
    {t : Tape K F // project t = s} ≃ Padding K F where
  toFun t := padding t.1
  invFun h := ⟨complete s h, project_complete s h⟩
  left_inv t := by
    apply Subtype.ext
    dsimp
    exact (congrArg (fun s => complete s (padding t.1)) t.2.symm).trans
      (complete_project t.1)
  right_inv := padding_complete s

theorem quotient_equal_fibres [Fintype K] (s : SourceTape K F) :
    Fintype.card {t : Tape K F // project t = s} = Fintype.card (Padding K F) :=
  Fintype.card_congr (quotientFibreEquiv s)

/-- The dependent row never reads word 0, including while summing the balance. -/
theorem balance_congr (u v : Fin 1024 → K)
    (same : ∀ r, r ≠ 0 → u r = v r) : balance 0 u = balance 0 v := by
  funext r
  simp only [balance]
  split_ifs
  · apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro s hs
    exact same s (Finset.ne_of_mem_erase hs)
  · exact same r (by assumption)

/-- Changing every ignored H1 coordinate leaves the model H1 padding intact. -/
theorem h1_completion (B : PackBasis F) (t : Tape K F) (h : Padding K F) :
    h1Padding B (Sum.elim t.2 (complete (project t) h).1) =
      h1Padding B (Sum.elim t.2 t.1) := by
  unfold h1Padding
  apply balance_congr
  intro r hr
  by_cases active : CopyActiveRow r
  · simp only [if_pos active]
  · simp only [if_neg active, extensionRaw, Sum.elim_inr]
    congr 1
    funext limb
    have hn : ¬ Ignored (.inr (1, r, limb)) := fun bad => bad.2.elim hr active
    exact congrArg (fun v : F => (v : K)) (dif_neg hn)

#print axioms project_complete
#print axioms padding_complete
#print axioms complete_project
#print axioms completion_equal_fibres
#print axioms quotient_equal_fibres
#print axioms balance_congr
#print axioms h1_completion
end R1Z.ProverCommitTapeCompletion
