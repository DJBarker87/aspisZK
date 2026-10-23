import AspisR1ActualSemanticRoundCutV1.Funs
import AspisR1OwnedPrefixRecordV2.Funs

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ActualSemanticRoundSourceModelV1
open AspisR1ActualSemanticRoundCutV1

abbrev QM := aspis_core.field.QM31
abbrev Out (H : Type) := core.result.Result (QM × (Array QM 10#usize) × r1_wire.SemanticTranscript H) r1_wire.Error

/-- The three functions omitted from the focused source owner. -/
structure Hooks where
  decode : (n : Usize) → r1_wire.ValidatedRecord → Usize →
    Result (core.result.Result (Array QM n) r1_wire.Error)
  boundary : Array QM 28#usize → Result QM
  neq : QM → QM → Result Bool
  value : Array QM 28#usize → Array QM 10#usize → Usize → Result QM

/-- Attempt26's exact cast-plus-wrapping row expression. -/
def sourceRow (round : Usize) : Result U8 := do
  let i ← lift (UScalar.cast .U8 round)
  lift (Std.U8.wrapping_add 15#u8 i)

/-- Continuation of attempt26 semantic_round once the source row is available. -/
def afterRow {H : Type} (B : Hooks) (D : aspis_core.digest.Digest32 H)
    (pref : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array QM 10#usize) (running : QM) (round : Usize) (row : U8) :
    Result (Out H) := do
  let r ← r1_wire.Prefix.validated_record pref row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 28#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let boundary ← B.boundary val
      let b ← B.neq boundary running
      if b then ok (.Err (.Boundary round)) else
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue vr1 =>
          let (r2, transcript1) ←
            r1_wire.SemanticTranscript.semantic_validated D transcript vr1
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let alpha1 ← Array.update alpha round val1
            let value ← B.value val alpha1 round
            ok (.Ok (value, alpha1, transcript1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (QM × (Array QM 10#usize) × r1_wire.SemanticTranscript H)
              (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (QM × (Array QM 10#usize) × r1_wire.SemanticTranscript H)
            (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (QM × (Array QM 10#usize) × r1_wire.SemanticTranscript H)
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (QM × (Array QM 10#usize) × r1_wire.SemanticTranscript H)
      (core.convert.FromSame r1_wire.Error) residual

/-- The actual source-shaped round: only three external method bodies are
parameters; row arithmetic and control flow are fixed and transparent. -/
def semanticRound {H : Type} (B : Hooks) (D : aspis_core.digest.Digest32 H)
    (pref : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array QM 10#usize) (running : QM) (round : Usize) :
    Result (Out H) := do
  let row ← sourceRow round
  afterRow B D pref transcript alpha running round row

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok p => cases p with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem update_set {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (x : α) (out : Array α n) (h : Array.update a i x = ok out) :
    out = a.set i x := by
  unfold Array.update at h
  split at h
  · cases h
  · exact (Result.ok.inj h).symm

/-- Invert the entire continuation, preserving the same record and transcript
call and the exact write output. -/
theorem afterRow_success_slots {H : Type} (B : Hooks)
    (D : aspis_core.digest.Digest32 H) (pref : r1_wire.Prefix)
    (transcript after : r1_wire.SemanticTranscript H)
    (alpha afterAlpha : Array QM 10#usize) (running out : QM)
    (round : Usize) (row : U8)
    (h : afterRow B D pref transcript alpha running round row =
      ok (.Ok (out, afterAlpha, after))) :
    ∃ record q, r1_wire.Prefix.validated_record pref row =
        ok (.Ok record) ∧
      r1_wire.SemanticTranscript.semantic_validated D transcript record =
        ok (.Ok q, after) ∧
      afterAlpha = alpha.set round q := by
  unfold afterRow at h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨recordret,hrecord,h⟩ := bind_success
    (r1_wire.Prefix.validated_record pref row) _ _ h
  have hok_record : ∃ x, recordret = core.result.Result.Ok x := by
    cases recordret with
    | Ok x => exact ⟨x,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨record,rfl⟩ := hok_record
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨polyret,hdecode,h⟩ := bind_success (B.decode 28#usize record 0#usize) _ _ h
  have hok_poly : ∃ x, polyret = core.result.Result.Ok x := by
    cases polyret with
    | Ok x => exact ⟨x,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨polynomial,rfl⟩ := hok_poly
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨boundary,hboundary,h⟩ := bind_success (B.boundary polynomial) _ _ h
  obtain ⟨bad,hcompare,h⟩ := bind_success
    (B.neq boundary running) _ _ h
  have hfalse : bad = false := by
    cases bad with
    | false => rfl
    | true => simp only [↓reduceIte] at h; cases h
  subst bad
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨sampleret,mid,hsemantic,h⟩ := pair_bind_success
    (r1_wire.SemanticTranscript.semantic_validated D transcript record) _ _ h
  have hok_q : ∃ x, sampleret = core.result.Result.Ok x := by
    cases sampleret with
    | Ok x => exact ⟨x,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨q,rfl⟩ := hok_q
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨nextAlpha,hupdate,h⟩ := bind_success (Array.update alpha round q) _ _ h
  have hset := update_set alpha round q nextAlpha hupdate
  obtain ⟨v,hvalue,h⟩ := bind_success (B.value polynomial nextAlpha round) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, lift, bind_tc_ok] at h
  have he := core.result.Result.Ok.inj (Result.ok.inj h)
  have ht : mid = after := congrArg (fun x => x.2.2) he
  have ha : nextAlpha = afterAlpha := congrArg (fun x => x.2.1) he
  refine ⟨record,q,hrecord,?_,ha.symm.trans hset⟩
  simpa only [ht] using hsemantic

/-- Whole-round success, not a separate body premise, yields the same-run
semantic call and alpha write. The row is the actual wrapping source result. -/
theorem semantic_round_success_slots {H : Type} (B : Hooks)
    (D : aspis_core.digest.Digest32 H) (pref : r1_wire.Prefix)
    (transcript after : r1_wire.SemanticTranscript H)
    (alpha afterAlpha : Array QM 10#usize) (running out : QM)
    (round : Usize)
    (h : semanticRound B D pref transcript alpha running round =
      ok (.Ok (out, afterAlpha, after))) :
    ∃ row record q, sourceRow round = ok row ∧
      r1_wire.Prefix.validated_record pref row = ok (.Ok record) ∧
      r1_wire.SemanticTranscript.semantic_validated D transcript record =
        ok (.Ok q, after) ∧
      afterAlpha = alpha.set round q := by
  unfold semanticRound at h
  obtain ⟨row,hrow,htail⟩ := bind_success (sourceRow round) _ _ h
  obtain ⟨record,q,hrecord,hsemantic,halpha⟩ :=
    afterRow_success_slots B D pref transcript after alpha afterAlpha running out round row htail
  exact ⟨row,record,q,hrow,hrecord,hsemantic,halpha⟩

#print axioms semantic_round_success_slots
end AspisR1ActualSemanticRoundSourceModelV1
