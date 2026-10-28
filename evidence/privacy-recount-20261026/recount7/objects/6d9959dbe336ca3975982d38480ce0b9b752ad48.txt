import R1Z.PhaseLocalityBin

/-! Dependency facts for the existing honest-view preparation and R1 folded
coefficient map. These are actual model functions, not replacement messages.
The byte encoder/leaf selection correspondence remains a source obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseBuilderDependenciesBin
open R0P R0P.SemSource R0Z R0Z.JointView R0Z.FsStatement R0Z.HonestView
  R0Z.MaskLayout R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin
  R1Z.PhaseScheduleBin R1Z.PhaseLocalityBin R1Z.TranscriptR1

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem prepare_local (pub : Public K) (t : Trace K) (ch ch' : R0Z.HonestView.Challenges K)
    (hl : ch.sem 0 = ch'.sem 0) (hc : ch.sem 1 = ch'.sem 1) :
    prepare pub t ch = prepare pub t ch' := by
  funext c r
  change (if c.val = 26 then helper pub t (ch.sem 0) (ch.sem 1) r else t c r) =
    (if c.val = 26 then helper pub t (ch'.sem 0) (ch'.sem 1) r else t c r)
  rw [hl, hc]

/-- Source C1 column selection: 0..25 and 28 (host_commitment.rs). -/
def c1Column (c : Fin 27) : Fin 29 :=
  if h : c.val < 26 then ⟨c.val, by omega⟩ else 28

theorem c1Column_not_helper (c : Fin 27) : (c1Column c).val ≠ 26 := by
  unfold c1Column
  split <;> simp_all <;> omega

/-- All 27 source C1 columns, including the mask columns, do not use even
lambda/chi. The helper column 26 belongs to C2. -/
theorem c1_challenge_free (pub : Public K) (t : Trace K) (B : PackBasis F)
    (τ : Tape K F) (ch : R0Z.HonestView.Challenges K) (c : Fin 27) :
    applyAff B (prepare pub (applyEligible t τ.2) ch) τ.1
        (c1Column c) =
      applyAff B (applyEligible t τ.2) τ.1 (c1Column c) := by
  funext r
  simp only [applyAff, prepare, if_neg (c1Column_not_helper c)]

/-- The entire prepared/masked trace depends on rows 0 and 1 only. -/
theorem prepared_at_c2 (W : R1Wire K CommitHandle Aux) (hd : DecodeLocal W.dec)
    (pub : Public K) (t : Trace K) (B : PackBasis F) (τ : Tape K F)
    (tr tr' : TRead → OracleAnswer) (he : SqAgree 33 tr tr') :
    applyAff B (prepare pub (applyEligible t τ.2) (chOf W tr)) τ.1 =
      applyAff B (prepare pub (applyEligible t τ.2) (chOf W tr')) τ.1 := by
  congr 1
  apply prepare_local
  · exact hd.sem _ _ _ _ _ _ _ _ 0 (he (.sqS 0) trivial (by decide))
  · exact hd.sem _ _ _ _ _ _ _ _ 1 (he (.sqS 1) trivial (by decide))

/-- The coefficient fold q1 uses gamma and alpha0, never alpha1 or queries. -/
theorem q1_local (π : Fin 1024 ≃ Fin 1024) (ch ch' : R0Z.HonestView.Challenges K)
    (hg : ch.opening 0 = ch'.opening 0) (ha : ch.opening 2 = ch'.opening 2) :
    q1 π ch = q1 π ch' := by
  simp only [q1, batchR1, hg, ha]

/-- The existing folded map on the existing prepared trace is available
after row 29, even if all subsequent answers differ. -/
theorem folded_at_29 (W : R1Wire K CommitHandle Aux) (hd : DecodeLocal W.dec)
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (t : Trace K)
    (B : PackBasis F) (τ : Tape K F) (tr tr' : TRead → OracleAnswer)
    (he : SqAgree 137 tr tr') :
    q1 π (chOf W tr) (applyAff B (prepare pub (applyEligible t τ.2) (chOf W tr)) τ.1) =
      q1 π (chOf W tr') (applyAff B (prepare pub (applyEligible t τ.2) (chOf W tr')) τ.1) := by
  have hp := prepared_at_c2 W hd pub t B τ tr tr'
    (fun j hj hlt => he j hj (lt_trans hlt (by decide)))
  have hq : q1 π (chOf W tr) = q1 π (chOf W tr') := by
    apply q1_local
    · exact hd.opening _ _ _ _ _ _ _ _ 0 (he (.sqO 0) trivial (by decide))
    · exact hd.opening _ _ _ _ _ _ _ _ 2 (he (.sqO 2) trivial (by decide))
  rw [hp, hq]

#print axioms prepare_local
#print axioms c1Column_not_helper
#print axioms c1_challenge_free
#print axioms prepared_at_c2
#print axioms q1_local
#print axioms folded_at_29
end R1Z.PhaseBuilderDependenciesBin
