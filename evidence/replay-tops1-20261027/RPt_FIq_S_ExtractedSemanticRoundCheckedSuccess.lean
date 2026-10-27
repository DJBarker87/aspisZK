import RPz7_ExtractedSemanticRoundsReachability

/-! Preserve the successful source-shaped round's decoded polynomial and both
arithmetic check outcomes. The earlier reachability theorem retained only the
record, challenge and alpha update. This theorem derives the actual boundary
comparison and evaluation from successful execution; it does not assume them.
The Boundaries implementations and whole verifier/caller reachability remain
explicit and must still be related to the concrete Rust helper. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SemanticRoundCheckedSuccess
open r1_wire
attribute [local instance] Classical.propDecidable
abbrev QM := aspis_core.field.QM31
-- Reuse the structural comparison proof from ActualFinishTerminalComparison.
private theorem qm_eq_source (x y : aspis_core.field.QM31) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y =
      ok (decide (x = y)) := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases y with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  by_cases ha : a = e <;> by_cases hb : b = f <;>
    by_cases hc : c = g <;> by_cases hd : d = h <;>
    simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ha, hb, hc, hd]

private theorem qm_ne_false_eq (x y : aspis_core.field.QM31)
    (h : core.cmp.PartialEq.ne.trait_default
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x y = ok false) :
    x = y := by
  simpa [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31, qm_eq_source] using h

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem update_set {α : Type} {n : Usize} (v : Array α n) (i : Usize)
    (x : α) (out : Array α n) (h : Array.update v i x = ok out) :
    out = v.set i x := by
  unfold Array.update at h
  split at h
  · cases h
  · exact (Result.ok.inj h).symm

theorem step_checks_of_success {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (beforeAlpha afterAlpha : Array QM 10#usize)
    (beforeRunning afterRunning : QM) (round : Usize) (row : U8)
    (hrow : 15#u8 + UScalar.cast .U8 round = ok row)
    (h : RoundModel.step B D pre self beforeAlpha beforeRunning round =
      ok (.Ok (afterRunning,afterAlpha,after))) :
    ∃ (record : ValidatedRecord) (polynomial : Array QM 28#usize)
      (boundary q : QM),
      Prefix.validated_record pre row = ok (.Ok record) ∧
      B.decode 28#usize record 0#usize = ok (.Ok polynomial) ∧
      B.boundary polynomial = ok boundary ∧
      core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary beforeRunning = ok false ∧
      boundary = beforeRunning ∧
      SemanticTranscript.semantic_validated D self record = ok (.Ok q,after) ∧
      afterAlpha = beforeAlpha.set round q ∧
      B.value polynomial afterAlpha round = ok afterRunning := by
  unfold RoundModel.step at h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok, hrow] at h
  obtain ⟨recordret,hrecord,h⟩ := bind_success (Prefix.validated_record pre row) _ _ h
  have hok_record : ∃ value, recordret = core.result.Result.Ok value := by
    cases recordret with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record,rfl⟩ := hok_record
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨polyret,hdecode,h⟩ := bind_success (B.decode 28#usize record 0#usize) _ _ h
  have hok_polynomial : ∃ value, polyret = core.result.Result.Ok value := by
    cases polyret with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨polynomial,rfl⟩ := hok_polynomial
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨boundary,hboundary,h⟩ := bind_success (B.boundary polynomial) _ _ h
  obtain ⟨bad,hcompare,h⟩ := bind_success
    (core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary beforeRunning) _ _ h
  have hfalse : bad = false := by
    cases bad with
    | false => rfl
    | true => simp only [↓reduceIte] at h; cases h
  subst bad
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨sampleret,mid,hsemantic,h⟩ := pair_bind_success
    (SemanticTranscript.semantic_validated D self record) _ _ h
  have hok_q : ∃ value, sampleret = core.result.Result.Ok value := by
    cases sampleret with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q,rfl⟩ := hok_q
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨nextAlpha,hupdate,h⟩ := bind_success (Array.update beforeAlpha round q) _ _ h
  have hset := update_set beforeAlpha round q nextAlpha hupdate
  obtain ⟨value,hvalue,h⟩ := bind_success (B.value polynomial nextAlpha round) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  have he := core.result.Result.Ok.inj (Result.ok.inj h)
  have ht : mid = after := congrArg (fun x => x.2.2) he
  have ha : nextAlpha = afterAlpha := congrArg (fun x => x.2.1) he
  have hv : value = afterRunning := congrArg (fun x => x.1) he
  refine ⟨record, polynomial, boundary, q, hrecord, hdecode, hboundary,
    hcompare, qm_ne_false_eq boundary beforeRunning hcompare, ?_, ha.symm.trans hset, ?_⟩
  · simpa only [ht] using hsemantic
  · simpa only [ha, hv] using hvalue


#print axioms step_checks_of_success
end AspisR1PublicPreparation.SemanticRoundCheckedSuccess
