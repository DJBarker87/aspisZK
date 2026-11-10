import NPH_R22JoinSM3
import NDO_JFv_RoundArithmetic
import RPz7_SemanticCallSelectedCanonical
import RPu_FIq_S_RawActualDecodeKMainAdapter
import NHI_ArrayCells

/-! NPH_ (R22, SC): the SemanticCallExtraction kernels on the tx1 semantic rounds.
- `step_congr`/`rounds_congr`: RoundModel.step and RoundModel.rounds with boundary/value replaced
  equal the originals whenever the replacements agree at the arguments the step passes: the
  boundary at the Ok decode(28, record, 0) coefficients, the value at those coefficients, the
  alpha array returned by the SAME successful Array.update with the Ok semantic_validated value,
  and the round. Bind-stepping through every outcome; rounds is unrolled over rounds 0..9.
- Deployed: AspisS1ExtractedRoundChildren.children (the op9 slot's R) has boundary =
  generatedMainBoundary and value = generatedMainValue. `Rg` runs them only on canonical
  coefficients (and, for value, round < 10 with canonical alpha[round]). Producers:
  decodeMain_success_members_canonical (coefficients), semantic_success_selected_canonical
  (alpha[round], via `update_at`). `deployed_rounds_guarded`: rounds over Rg = rounds over
  children, with no premise. `finish_rounds_guarded`: the same inside FinishModel.finish.
- Site lemmas: wherever Rg runs generatedMainBoundary/generatedMainValue, the WHOLE entry call is
  ok with canonical output (JFv_RoundArithmetic.boundary/value), so every SC kernel call it
  executes returns ok. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSC1
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1.NPH_R22JoinSM3 (bind_congr_ok branch_cont)

abbrev Q := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev BdT := Array Q 28#usize → Result Q
abbrev VlT := Array Q 28#usize → Array Q 10#usize → Usize → Result Q

theorem update_at {T : Type} {n : Usize} (a b : Array T n) (i : Usize) (v : T)
    (run : Array.update a i v = ok b) : i.val < a.val.length ∧ b.val[i.val]? = some v := by
  by_cases hi : i.val < n.val
  · have e := (NHI_ArrayCells.update a i v hi).symm.trans run
    cases Result.ok.inj e
    refine ⟨by rw [a.property]; exact hi, NHI_ArrayCells.selected a i v hi⟩
  · exfalso
    have hl : ¬ i.val < a.val.length := by rw [a.property]; exact hi
    unfold Array.update at run
    simp only [Array.getElem?_Usize_eq, List.getElem?_eq_none (Nat.le_of_not_lt hl)] at run
    first | cases run | simp at run
#print axioms update_at

theorem step_congr (B : RoundModel.Boundaries) (bd' : BdT) (vl' : VlT) {H : Type}
    (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (alpha : Array Q 10#usize) (running : Q) (round : Usize)
    (hbd : ∀ (vr : r1_wire.ValidatedRecord) (val : Array Q 28#usize),
      B.decode 28#usize vr 0#usize = ok (.Ok val) → bd' val = B.boundary val)
    (hvl : ∀ (vr : r1_wire.ValidatedRecord) (val : Array Q 28#usize) (val1 : Q)
      (t1 : r1_wire.SemanticTranscript H) (alpha1 : Array Q 10#usize),
      B.decode 28#usize vr 0#usize = ok (.Ok val) →
      r1_wire.SemanticTranscript.semantic_validated D t vr = ok (.Ok val1, t1) →
      Array.update alpha round val1 = ok alpha1 → vl' val alpha1 round = B.value val alpha1 round) :
    RoundModel.step { B with boundary := bd', value := vl' } D pre t alpha running round =
      RoundModel.step B D pre t alpha running round := by
  unfold RoundModel.step
  refine bind_congr_ok _ _ _ (fun i _ => ?_)
  refine bind_congr_ok _ _ _ (fun row _ => ?_)
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break res => dsimp only
  | Continue vr =>
  have hrv : r = .Ok vr := (branch_cont r vr).1 hcf
  refine bind_congr_ok _ _ _ (fun r1 hr1 => ?_)
  refine bind_congr_ok _ _ _ (fun cf1 hcf1 => ?_)
  cases cf1 with
  | Break res => dsimp only
  | Continue val =>
  have hdec : B.decode 28#usize vr 0#usize = ok (.Ok val) := by
    have e := (branch_cont r1 val).1 hcf1; subst e; exact hr1
  show (bd' val >>= _) = _
  rw [hbd vr val hdec]
  refine bind_congr_ok _ _ _ (fun bnd _ => ?_)
  refine bind_congr_ok _ _ _ (fun b _ => ?_)
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, if_false]
    refine bind_congr_ok _ _ _ (fun cf2 hcf2 => ?_)
    cases cf2 with
    | Break res => dsimp only
    | Continue vr1 =>
    have e1 := (branch_cont r vr1).1 hcf2
    rw [hrv] at e1
    cases e1
    refine bind_congr_ok _ _ _ (fun x hx => ?_)
    obtain ⟨r2, t1⟩ := x
    refine bind_congr_ok _ _ _ (fun cf3 hcf3 => ?_)
    cases cf3 with
    | Break res => dsimp only
    | Continue val1 =>
    have hsv : r1_wire.SemanticTranscript.semantic_validated D t vr = ok (.Ok val1, t1) := by
      have e := (branch_cont r2 val1).1 hcf3; subst e; exact hx
    refine bind_congr_ok _ _ _ (fun alpha1 hal => ?_)
    show (vl' val alpha1 round >>= _) = _
    rw [hvl vr val val1 t1 alpha1 hdec hsv hal]
  · simp only [↓reduceIte, if_true]
#print axioms step_congr

theorem rounds_congr (B : RoundModel.Boundaries) (bd' : BdT) (vl' : VlT) {H : Type}
    (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (hbd : ∀ (vr : r1_wire.ValidatedRecord) (val : Array Q 28#usize),
      B.decode 28#usize vr 0#usize = ok (.Ok val) → bd' val = B.boundary val)
    (hvl : ∀ (t' : r1_wire.SemanticTranscript H) (alpha : Array Q 10#usize) (round : Usize)
      (vr : r1_wire.ValidatedRecord) (val : Array Q 28#usize) (val1 : Q)
      (t1 : r1_wire.SemanticTranscript H) (alpha1 : Array Q 10#usize),
      B.decode 28#usize vr 0#usize = ok (.Ok val) →
      r1_wire.SemanticTranscript.semantic_validated D t' vr = ok (.Ok val1, t1) →
      Array.update alpha round val1 = ok alpha1 → vl' val alpha1 round = B.value val alpha1 round) :
    RoundModel.rounds { B with boundary := bd', value := vl' } D pre t = RoundModel.rounds B D pre t := by
  have hs : ∀ (t' : r1_wire.SemanticTranscript H) (alpha : Array Q 10#usize) (running : Q) (round : Usize),
      RoundModel.step { B with boundary := bd', value := vl' } D pre t' alpha running round =
        RoundModel.step B D pre t' alpha running round :=
    fun t' alpha running round => step_congr B bd' vl' D pre t' alpha running round hbd
      (fun vr val val1 t1 alpha1 => hvl t' alpha round vr val val1 t1 alpha1)
  unfold RoundModel.rounds
  simp only [hs]
#print axioms rounds_congr

abbrev Canon (x : Q) : Prop := AspisR1.JFv_RoundArithmetic.Canonical x

open Classical in
def gbd (p : Array Q 28#usize) : Result Q :=
  if ∀ x ∈ p.val, Canon x then AspisS1ExtractedRoundChildren.generatedMainBoundary p
  else fail Aeneas.Std.Error.panic

open Classical in
def gvl (p : Array Q 28#usize) (alpha : Array Q 10#usize) (round : Usize) : Result Q :=
  if round.val < 10 ∧ (∀ x, alpha.val[round.val]? = some x → Canon x) ∧ ∀ x ∈ p.val, Canon x then
    AspisS1ExtractedRoundChildren.generatedMainValue p alpha round
  else fail Aeneas.Std.Error.panic

abbrev Rg : RoundModel.Boundaries :=
  { AspisS1ExtractedRoundChildren.children with boundary := gbd, value := gvl }

theorem decode_canon (vr : r1_wire.ValidatedRecord) (val : Array Q 28#usize)
    (h : AspisS1ExtractedRoundChildren.children.decode 28#usize vr 0#usize = ok (.Ok val)) :
    ∀ x ∈ val.val, Canon x :=
  fun x hx => RawActualDecodeKMainAdapter.decodeMain_success_members_canonical 28#usize vr 0#usize val h x hx
#print axioms decode_canon

theorem deployed_rounds_guarded {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (t : r1_wire.SemanticTranscript H) :
    RoundModel.rounds Rg D pre t = RoundModel.rounds AspisS1ExtractedRoundChildren.children D pre t := by
  apply rounds_congr
  · intro vr val hdec
    show gbd val = AspisS1ExtractedRoundChildren.generatedMainBoundary val
    unfold gbd
    rw [if_pos (decode_canon vr val hdec)]
  · intro t' alpha round vr val val1 t1 alpha1 hdec hsv hupd
    have hv1 : Canon val1 :=
      SemanticRoundAlphaSelectedCanonical.SemanticCallSelectedCanonical.semantic_success_selected_canonical
        D t' t1 vr val1 hsv
    obtain ⟨hl, hget⟩ := update_at alpha alpha1 round val1 hupd
    have hlen : alpha.val.length = 10 := alpha.property
    have hr : round.val < 10 := by omega
    have hal : ∀ x, alpha1.val[round.val]? = some x → Canon x := by
      intro x hx
      rw [hget] at hx
      cases hx
      exact hv1
    show gvl val alpha1 round = AspisS1ExtractedRoundChildren.generatedMainValue val alpha1 round
    unfold gvl
    rw [if_pos ⟨hr, hal, decode_canon vr val hdec⟩]
#print axioms deployed_rounds_guarded

theorem finish_rounds_guarded (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    FinishModel.finish Rg B D pub pre t ch obs =
      FinishModel.finish AspisS1ExtractedRoundChildren.children B D pub pre t ch obs := by
  unfold FinishModel.finish
  simp only [deployed_rounds_guarded]
#print axioms finish_rounds_guarded

theorem guarded_boundary_site (p : Array Q 28#usize) :
    gbd p = fail Aeneas.Std.Error.panic ∨
    ((∀ x ∈ p.val, Canon x) ∧ gbd p = AspisS1ExtractedRoundChildren.generatedMainBoundary p ∧
      ∃ out, AspisS1ExtractedRoundChildren.generatedMainBoundary p = ok out ∧ Canon out) := by
  by_cases hc : ∀ x ∈ p.val, Canon x
  · right
    refine ⟨hc, by unfold gbd; rw [if_pos hc], ?_⟩
    exact AspisR1.JFv_RoundArithmetic.boundary p (fun i => hc _ (List.getElem_mem _))
  · left
    unfold gbd
    rw [if_neg hc]
#print axioms guarded_boundary_site

theorem guarded_value_site (p : Array Q 28#usize) (alpha : Array Q 10#usize) (round : Usize) :
    gvl p alpha round = fail Aeneas.Std.Error.panic ∨
    (round.val < 10 ∧ gvl p alpha round = AspisS1ExtractedRoundChildren.generatedMainValue p alpha round ∧
      ∃ out, AspisS1ExtractedRoundChildren.generatedMainValue p alpha round = ok out ∧ Canon out) := by
  by_cases hc : round.val < 10 ∧ (∀ x, alpha.val[round.val]? = some x → Canon x) ∧ ∀ x ∈ p.val, Canon x
  · right
    refine ⟨hc.1, by unfold gvl; rw [if_pos hc], ?_⟩
    have hlen : alpha.val.length = 10 := alpha.property
    have hb : round.val < alpha.val.length := by omega
    exact AspisR1.JFv_RoundArithmetic.value p alpha round hc.1
      (hc.2.1 _ (List.getElem?_eq_getElem hb)) (fun i => hc.2.2 _ (List.getElem_mem _))
  · left
    unfold gvl
    rw [if_neg hc]
#print axioms guarded_value_site

end AspisR1.NPH_R22JoinSC1
