import RPz7_ExtractedDigest32Callers
/-! Every call in the actual straight-line begin succeeds on acceptance. The
trace is a relation over the extracted functions, retaining exact validated
records and state carry, with no supplied successful-call premises. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.BeginCalls
open r1_wire CallerStep

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a, b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a, b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a, b, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem index_mut_back {α : Type} {n : Usize} (v : Array α n) (i : Usize)
    (out : α × (α → Array α n)) (h : Array.index_mut_usize v i = ok out) :
    out.2 = Aeneas.Std.Array.set v i := by
  unfold Array.index_mut_usize at h
  obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  exact (congrArg Prod.snd (Result.ok.inj h)).symm

inductive SemanticRun {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix) :
    List U8 → SemanticTranscript H → SemanticTranscript H → List aspis_core.field.QM31 → Prop
  | nil (self) : SemanticRun D pre [] self self []
  | cons {row rows self mid after q qs record}
      (hrecord : Prefix.validated_record pre row = ok (.Ok record))
      (hsemantic : SemanticTranscript.semantic_validated D self record = ok (.Ok q, mid))
      (tail : SemanticRun D pre rows mid after qs) :
      SemanticRun D pre (row :: rows) self after (q :: qs)

theorem SemanticRun.length {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rows self after qs} (h : SemanticRun D pre rows self after qs) :
    qs.length = rows.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp only [List.length_cons, ih]

theorem SemanticRun.carry {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rows self after qs} (h : SemanticRun D pre rows self after qs) :
    after.hash = self.hash ∧ after.next_row.val = self.next_row.val + rows.length := by
  induction h with
  | nil => exact ⟨rfl, by simp⟩
  | @cons row rows self mid after q qs record hr hs tail ih =>
    obtain ⟨hrow, block, tag, next, absorbed, state, ht, hn, ha, hb, hc, hq, he⟩ :=
      CallerStep.semantic_step_success D self mid record q hs
    constructor
    · simpa only [he] using ih.1
    · rw [he] at ih
      simp only [List.length_cons]
      rw [ih.2, hn, hrow]
      omega

def rows : List U8 := [0#u8,1#u8,2#u8,3#u8,4#u8,5#u8,6#u8,7#u8,8#u8,9#u8,10#u8,11#u8,12#u8,13#u8,14#u8]

def challengeList (out : Challenges) : List aspis_core.field.QM31 :=
  out.lambda :: out.chi :: out.theta :: (out.zc.val ++ [out.mu, out.eta])

/-- All fifteen source calls, including the ten zc rows, are reached in order.
The output challenges are the actual values returned by those same calls. -/
theorem begin_success {H : Type} (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (out : Challenges)
    (h : begin D pre self = ok (.Ok out, after)) :
    ∃ qs, SemanticRun D pre rows self after qs ∧ qs = challengeList out := by
  unfold begin at h
  obtain ⟨r0, hr0, h⟩ := bind_success (Prefix.validated_record pre 0#u8) _ _ h
  have hok0 : ∃ record, r0 = core.result.Result.Ok record := by
    cases r0 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record0, rfl⟩ := hok0
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret0, t1, hs0, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D self record0) _ _ h
  have hqok0 : ∃ q, ret0 = core.result.Result.Ok q := by
    cases ret0 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q0, rfl⟩ := hqok0
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨r1, hr1, h⟩ := bind_success (Prefix.validated_record pre 1#u8) _ _ h
  have hok1 : ∃ record, r1 = core.result.Result.Ok record := by
    cases r1 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record1, rfl⟩ := hok1
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret1, t2, hs1, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t1 record1) _ _ h
  have hqok1 : ∃ q, ret1 = core.result.Result.Ok q := by
    cases ret1 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q1, rfl⟩ := hqok1
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨r2, hr2, h⟩ := bind_success (Prefix.validated_record pre 2#u8) _ _ h
  have hok2 : ∃ record, r2 = core.result.Result.Ok record := by
    cases r2 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record2, rfl⟩ := hok2
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret2, t3, hs2, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t2 record2) _ _ h
  have hqok2 : ∃ q, ret2 = core.result.Result.Ok q := by
    cases ret2 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q2, rfl⟩ := hqok2
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨r3, hr3, h⟩ := bind_success (Prefix.validated_record pre 3#u8) _ _ h
  have hok3 : ∃ record, r3 = core.result.Result.Ok record := by
    cases r3 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record3, rfl⟩ := hok3
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret3, t4, hs3, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t3 record3) _ _ h
  have hqok3 : ∃ q, ret3 = core.result.Result.Ok q := by
    cases ret3 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q3, rfl⟩ := hqok3
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old3, back3, hedit3, h⟩ := pair_bind_success (Array.index_mut_usize (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback3 := index_mut_back _ _ (old3, back3) hedit3
  change back3 = _ at hback3
  rw [hback3] at h
  obtain ⟨r4, hr4, h⟩ := bind_success (Prefix.validated_record pre 4#u8) _ _ h
  have hok4 : ∃ record, r4 = core.result.Result.Ok record := by
    cases r4 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record4, rfl⟩ := hok4
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret4, t5, hs4, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t4 record4) _ _ h
  have hqok4 : ∃ q, ret4 = core.result.Result.Ok q := by
    cases ret4 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q4, rfl⟩ := hqok4
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old4, back4, hedit4, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback4 := index_mut_back _ _ (old4, back4) hedit4
  change back4 = _ at hback4
  rw [hback4] at h
  obtain ⟨r5, hr5, h⟩ := bind_success (Prefix.validated_record pre 5#u8) _ _ h
  have hok5 : ∃ record, r5 = core.result.Result.Ok record := by
    cases r5 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record5, rfl⟩ := hok5
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret5, t6, hs5, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t5 record5) _ _ h
  have hqok5 : ∃ q, ret5 = core.result.Result.Ok q := by
    cases ret5 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q5, rfl⟩ := hqok5
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old5, back5, hedit5, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback5 := index_mut_back _ _ (old5, back5) hedit5
  change back5 = _ at hback5
  rw [hback5] at h
  obtain ⟨r6, hr6, h⟩ := bind_success (Prefix.validated_record pre 6#u8) _ _ h
  have hok6 : ∃ record, r6 = core.result.Result.Ok record := by
    cases r6 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record6, rfl⟩ := hok6
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret6, t7, hs6, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t6 record6) _ _ h
  have hqok6 : ∃ q, ret6 = core.result.Result.Ok q := by
    cases ret6 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q6, rfl⟩ := hqok6
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old6, back6, hedit6, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback6 := index_mut_back _ _ (old6, back6) hedit6
  change back6 = _ at hback6
  rw [hback6] at h
  obtain ⟨r7, hr7, h⟩ := bind_success (Prefix.validated_record pre 7#u8) _ _ h
  have hok7 : ∃ record, r7 = core.result.Result.Ok record := by
    cases r7 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record7, rfl⟩ := hok7
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret7, t8, hs7, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t7 record7) _ _ h
  have hqok7 : ∃ q, ret7 = core.result.Result.Ok q := by
    cases ret7 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q7, rfl⟩ := hqok7
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old7, back7, hedit7, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback7 := index_mut_back _ _ (old7, back7) hedit7
  change back7 = _ at hback7
  rw [hback7] at h
  obtain ⟨r8, hr8, h⟩ := bind_success (Prefix.validated_record pre 8#u8) _ _ h
  have hok8 : ∃ record, r8 = core.result.Result.Ok record := by
    cases r8 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record8, rfl⟩ := hok8
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret8, t9, hs8, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t8 record8) _ _ h
  have hqok8 : ∃ q, ret8 = core.result.Result.Ok q := by
    cases ret8 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q8, rfl⟩ := hqok8
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old8, back8, hedit8, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize q7) 5#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback8 := index_mut_back _ _ (old8, back8) hedit8
  change back8 = _ at hback8
  rw [hback8] at h
  obtain ⟨r9, hr9, h⟩ := bind_success (Prefix.validated_record pre 9#u8) _ _ h
  have hok9 : ∃ record, r9 = core.result.Result.Ok record := by
    cases r9 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record9, rfl⟩ := hok9
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret9, t10, hs9, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t9 record9) _ _ h
  have hqok9 : ∃ q, ret9 = core.result.Result.Ok q := by
    cases ret9 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q9, rfl⟩ := hqok9
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old9, back9, hedit9, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize q7) 5#usize q8) 6#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback9 := index_mut_back _ _ (old9, back9) hedit9
  change back9 = _ at hback9
  rw [hback9] at h
  obtain ⟨r10, hr10, h⟩ := bind_success (Prefix.validated_record pre 10#u8) _ _ h
  have hok10 : ∃ record, r10 = core.result.Result.Ok record := by
    cases r10 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record10, rfl⟩ := hok10
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret10, t11, hs10, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t10 record10) _ _ h
  have hqok10 : ∃ q, ret10 = core.result.Result.Ok q := by
    cases ret10 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q10, rfl⟩ := hqok10
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old10, back10, hedit10, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize q7) 5#usize q8) 6#usize q9) 7#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback10 := index_mut_back _ _ (old10, back10) hedit10
  change back10 = _ at hback10
  rw [hback10] at h
  obtain ⟨r11, hr11, h⟩ := bind_success (Prefix.validated_record pre 11#u8) _ _ h
  have hok11 : ∃ record, r11 = core.result.Result.Ok record := by
    cases r11 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record11, rfl⟩ := hok11
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret11, t12, hs11, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t11 record11) _ _ h
  have hqok11 : ∃ q, ret11 = core.result.Result.Ok q := by
    cases ret11 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q11, rfl⟩ := hqok11
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old11, back11, hedit11, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize q7) 5#usize q8) 6#usize q9) 7#usize q10) 8#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback11 := index_mut_back _ _ (old11, back11) hedit11
  change back11 = _ at hback11
  rw [hback11] at h
  obtain ⟨r12, hr12, h⟩ := bind_success (Prefix.validated_record pre 12#u8) _ _ h
  have hok12 : ∃ record, r12 = core.result.Result.Ok record := by
    cases r12 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record12, rfl⟩ := hok12
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret12, t13, hs12, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t12 record12) _ _ h
  have hqok12 : ∃ q, ret12 = core.result.Result.Ok q := by
    cases ret12 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q12, rfl⟩ := hqok12
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨old12, back12, hedit12, h⟩ := pair_bind_success (Array.index_mut_usize (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize q3) 1#usize q4) 2#usize q5) 3#usize q6) 4#usize q7) 5#usize q8) 6#usize q9) 7#usize q10) 8#usize q11) 9#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  have hback12 := index_mut_back _ _ (old12, back12) hedit12
  change back12 = _ at hback12
  rw [hback12] at h
  obtain ⟨r13, hr13, h⟩ := bind_success (Prefix.validated_record pre 13#u8) _ _ h
  have hok13 : ∃ record, r13 = core.result.Result.Ok record := by
    cases r13 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record13, rfl⟩ := hok13
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret13, t14, hs13, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t13 record13) _ _ h
  have hqok13 : ∃ q, ret13 = core.result.Result.Ok q := by
    cases ret13 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q13, rfl⟩ := hqok13
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨r14, hr14, h⟩ := bind_success (Prefix.validated_record pre 14#u8) _ _ h
  have hok14 : ∃ record, r14 = core.result.Result.Ok record := by
    cases r14 with
    | Ok record => exact ⟨record, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record14, rfl⟩ := hok14
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨ret14, t15, hs14, h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D t14 record14) _ _ h
  have hqok14 : ∃ q, ret14 = core.result.Result.Ok q := by
    cases ret14 with
    | Ok q => exact ⟨q, rfl⟩
    | Err e =>
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q14, rfl⟩ := hqok14
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  have ht : t15 = after := congrArg Prod.snd (Result.ok.inj h)
  have hout := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
  rw [← ht]
  refine ⟨[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14], ?_, ?_⟩
  · unfold rows
    apply SemanticRun.cons hr0 hs0
    apply SemanticRun.cons hr1 hs1
    apply SemanticRun.cons hr2 hs2
    apply SemanticRun.cons hr3 hs3
    apply SemanticRun.cons hr4 hs4
    apply SemanticRun.cons hr5 hs5
    apply SemanticRun.cons hr6 hs6
    apply SemanticRun.cons hr7 hs7
    apply SemanticRun.cons hr8 hs8
    apply SemanticRun.cons hr9 hs9
    apply SemanticRun.cons hr10 hs10
    apply SemanticRun.cons hr11 hs11
    apply SemanticRun.cons hr12 hs12
    apply SemanticRun.cons hr13 hs13
    apply SemanticRun.cons hr14 hs14
    exact SemanticRun.nil t15
  · rw [← hout]
    rfl

theorem begin_carry {H : Type} (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (out : Challenges)
    (h : begin D pre self = ok (.Ok out, after)) :
    after.hash = self.hash ∧ after.next_row.val = self.next_row.val + 15 := by
  obtain ⟨qs, hs, hqs⟩ := begin_success D pre self after out h
  simpa only [rows, List.length_cons, List.length_nil, Nat.reduceAdd] using hs.carry D pre

#print axioms SemanticRun.length
#print axioms SemanticRun.carry
#print axioms begin_success
#print axioms begin_carry
end AspisR1PublicPreparation.BeginCalls
