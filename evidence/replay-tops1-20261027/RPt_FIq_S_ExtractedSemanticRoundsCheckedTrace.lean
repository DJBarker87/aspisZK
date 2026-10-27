import RPt_FIq_S_ExtractedSemanticRoundCheckedSuccess

/-! Successful execution of the maintained ten-step source-shaped semantic
helper retains every checked decoded polynomial, boundary equality, challenge
and evaluation, in execution order. It also retains the initial row-14 decode.
The arithmetic/decode Boundaries and whole-verifier caller correspondence are
still explicit; no acceptance-to-LiteralChecks theorem is claimed here. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SemanticRoundsCheckedTrace
open r1_wire RoundCalls
abbrev QM := aspis_core.field.QM31
abbrev Outcome (H : Type) := QM × Array QM 10#usize × SemanticTranscript H

def CheckedStep {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : Prefix) (before after : Outcome H) (round : Usize) (row : U8) : Prop :=
  ∃ (record : ValidatedRecord) (polynomial : Array QM 28#usize) (boundary q : QM),
    Prefix.validated_record pre row = ok (.Ok record) ∧
    B.decode 28#usize record 0#usize = ok (.Ok polynomial) ∧
    B.boundary polynomial = ok boundary ∧
    core.cmp.PartialEq.ne.trait_default
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary before.1 = ok false ∧
    boundary = before.1 ∧
    SemanticTranscript.semantic_validated D before.2.2 record = ok (.Ok q, after.2.2) ∧
    after.2.1 = before.2.1.set round q ∧
    B.value polynomial after.2.1 round = ok after.1

inductive CheckedRun {H : Type} (B : RoundModel.Boundaries)
    (D : aspis_core.Digest32 H) (pre : Prefix) :
    List (Usize × U8) → Outcome H → Outcome H → Prop
  | nil (out : Outcome H) : CheckedRun B D pre [] out out
  | cons {round : Usize} {row : U8} {rest : List (Usize × U8)}
      {before mid after : Outcome H}
      (checked : CheckedStep B D pre before mid round row)
      (tail : CheckedRun B D pre rest mid after) :
      CheckedRun B D pre ((round, row) :: rest) before after

def schedule : List (Usize × U8) :=
  [(0#usize,15#u8),(1#usize,16#u8),(2#usize,17#u8),(3#usize,18#u8),
   (4#usize,19#u8),(5#usize,20#u8),(6#usize,21#u8),(7#usize,22#u8),
   (8#usize,23#u8),(9#usize,24#u8)]

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
private theorem add_exact {ty : UScalarTy} (a b c : UScalar ty)
    (hc : c.val = a.val + b.val) : a + b = ok c := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := a) (y := b) (by scalar_tac))
  have he : z = c := by scalar_tac
  simpa only [he] using hz


theorem rounds_checked_success {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (running : QM)
    (alpha : Array QM 10#usize)
    (h : RoundModel.rounds B D pre self = ok (.Ok (running,alpha,after))) :
    ∃ (record : ValidatedRecord) (decoded : Array QM 1#usize) (initial : QM),
      Prefix.validated_record pre 14#u8 = ok (.Ok record) ∧
      B.decode 1#usize record 0#usize = ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize = ok initial ∧
      CheckedRun B D pre schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, self)
        (running, alpha, after) := by
  have hrow0 : 15#u8 + UScalar.cast .U8 0#usize = ok 15#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow1 : 15#u8 + UScalar.cast .U8 1#usize = ok 16#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow2 : 15#u8 + UScalar.cast .U8 2#usize = ok 17#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow3 : 15#u8 + UScalar.cast .U8 3#usize = ok 18#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow4 : 15#u8 + UScalar.cast .U8 4#usize = ok 19#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow5 : 15#u8 + UScalar.cast .U8 5#usize = ok 20#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow6 : 15#u8 + UScalar.cast .U8 6#usize = ok 21#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow7 : 15#u8 + UScalar.cast .U8 7#usize = ok 22#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow8 : 15#u8 + UScalar.cast .U8 8#usize = ok 23#u8 := add_exact _ _ _ (by scalar_tac)
  have hrow9 : 15#u8 + UScalar.cast .U8 9#usize = ok 24#u8 := add_exact _ _ _ (by scalar_tac)
  unfold RoundModel.rounds at h
  obtain ⟨initret,hinitrecord,h⟩ := bind_success (Prefix.validated_record pre 14#u8) _ _ h
  have hok_initrecord : ∃ value, initret = core.result.Result.Ok value := by
    cases initret with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨initrecord,rfl⟩ := hok_initrecord
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨initvalues,hinitdecode,h⟩ := bind_success (B.decode 1#usize initrecord 0#usize) _ _ h
  have hok_decoded_initial : ∃ value, initvalues = core.result.Result.Ok value := by
    cases initvalues with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨decoded_initial,rfl⟩ := hok_decoded_initial
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨initial,hinitindex,h⟩ := bind_success (Array.index_usize decoded_initial 0#usize) _ _ h
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨stepret0,hstep0,h⟩ := bind_success (RoundModel.step B D pre self (Array.repeat 10#usize aspis_core.field.QM31.ZERO) initial 0#usize) _ _ h
  have hok_tuple0 : ∃ value, stepret0 = core.result.Result.Ok value := by
    cases stepret0 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple0,rfl⟩ := hok_tuple0
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value0,alpha1,t1⟩ := tuple0
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record0,q0,hr0,hs0,hset0⟩ := step_success B D pre self t1 (Array.repeat 10#usize aspis_core.field.QM31.ZERO) alpha1 initial value0 0#usize 15#u8 hrow0 hstep0
  have hc0 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre self t1 (Array.repeat 10#usize aspis_core.field.QM31.ZERO) alpha1 initial value0 0#usize 15#u8 hrow0 hstep0
  subst alpha1
  obtain ⟨stepret1,hstep1,h⟩ := bind_success (RoundModel.step B D pre t1 ((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0) value0 1#usize) _ _ h
  have hok_tuple1 : ∃ value, stepret1 = core.result.Result.Ok value := by
    cases stepret1 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple1,rfl⟩ := hok_tuple1
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value1,alpha2,t2⟩ := tuple1
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record1,q1,hr1,hs1,hset1⟩ := step_success B D pre t1 t2 ((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0) alpha2 value0 value1 1#usize 16#u8 hrow1 hstep1
  have hc1 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t1 t2 ((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0) alpha2 value0 value1 1#usize 16#u8 hrow1 hstep1
  subst alpha2
  obtain ⟨stepret2,hstep2,h⟩ := bind_success (RoundModel.step B D pre t2 (((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1) value1 2#usize) _ _ h
  have hok_tuple2 : ∃ value, stepret2 = core.result.Result.Ok value := by
    cases stepret2 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple2,rfl⟩ := hok_tuple2
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value2,alpha3,t3⟩ := tuple2
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record2,q2,hr2,hs2,hset2⟩ := step_success B D pre t2 t3 (((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1) alpha3 value1 value2 2#usize 17#u8 hrow2 hstep2
  have hc2 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t2 t3 (((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1) alpha3 value1 value2 2#usize 17#u8 hrow2 hstep2
  subst alpha3
  obtain ⟨stepret3,hstep3,h⟩ := bind_success (RoundModel.step B D pre t3 ((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2) value2 3#usize) _ _ h
  have hok_tuple3 : ∃ value, stepret3 = core.result.Result.Ok value := by
    cases stepret3 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple3,rfl⟩ := hok_tuple3
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value3,alpha4,t4⟩ := tuple3
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record3,q3,hr3,hs3,hset3⟩ := step_success B D pre t3 t4 ((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2) alpha4 value2 value3 3#usize 18#u8 hrow3 hstep3
  have hc3 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t3 t4 ((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2) alpha4 value2 value3 3#usize 18#u8 hrow3 hstep3
  subst alpha4
  obtain ⟨stepret4,hstep4,h⟩ := bind_success (RoundModel.step B D pre t4 (((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3) value3 4#usize) _ _ h
  have hok_tuple4 : ∃ value, stepret4 = core.result.Result.Ok value := by
    cases stepret4 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple4,rfl⟩ := hok_tuple4
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value4,alpha5,t5⟩ := tuple4
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record4,q4,hr4,hs4,hset4⟩ := step_success B D pre t4 t5 (((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3) alpha5 value3 value4 4#usize 19#u8 hrow4 hstep4
  have hc4 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t4 t5 (((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3) alpha5 value3 value4 4#usize 19#u8 hrow4 hstep4
  subst alpha5
  obtain ⟨stepret5,hstep5,h⟩ := bind_success (RoundModel.step B D pre t5 ((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4) value4 5#usize) _ _ h
  have hok_tuple5 : ∃ value, stepret5 = core.result.Result.Ok value := by
    cases stepret5 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple5,rfl⟩ := hok_tuple5
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value5,alpha6,t6⟩ := tuple5
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record5,q5,hr5,hs5,hset5⟩ := step_success B D pre t5 t6 ((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4) alpha6 value4 value5 5#usize 20#u8 hrow5 hstep5
  have hc5 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t5 t6 ((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4) alpha6 value4 value5 5#usize 20#u8 hrow5 hstep5
  subst alpha6
  obtain ⟨stepret6,hstep6,h⟩ := bind_success (RoundModel.step B D pre t6 (((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5) value5 6#usize) _ _ h
  have hok_tuple6 : ∃ value, stepret6 = core.result.Result.Ok value := by
    cases stepret6 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple6,rfl⟩ := hok_tuple6
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value6,alpha7,t7⟩ := tuple6
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record6,q6,hr6,hs6,hset6⟩ := step_success B D pre t6 t7 (((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5) alpha7 value5 value6 6#usize 21#u8 hrow6 hstep6
  have hc6 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t6 t7 (((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5) alpha7 value5 value6 6#usize 21#u8 hrow6 hstep6
  subst alpha7
  obtain ⟨stepret7,hstep7,h⟩ := bind_success (RoundModel.step B D pre t7 ((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6) value6 7#usize) _ _ h
  have hok_tuple7 : ∃ value, stepret7 = core.result.Result.Ok value := by
    cases stepret7 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple7,rfl⟩ := hok_tuple7
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value7,alpha8,t8⟩ := tuple7
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record7,q7,hr7,hs7,hset7⟩ := step_success B D pre t7 t8 ((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6) alpha8 value6 value7 7#usize 22#u8 hrow7 hstep7
  have hc7 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t7 t8 ((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6) alpha8 value6 value7 7#usize 22#u8 hrow7 hstep7
  subst alpha8
  obtain ⟨stepret8,hstep8,h⟩ := bind_success (RoundModel.step B D pre t8 (((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7) value7 8#usize) _ _ h
  have hok_tuple8 : ∃ value, stepret8 = core.result.Result.Ok value := by
    cases stepret8 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple8,rfl⟩ := hok_tuple8
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value8,alpha9,t9⟩ := tuple8
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record8,q8,hr8,hs8,hset8⟩ := step_success B D pre t8 t9 (((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7) alpha9 value7 value8 8#usize 23#u8 hrow8 hstep8
  have hc8 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t8 t9 (((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7) alpha9 value7 value8 8#usize 23#u8 hrow8 hstep8
  subst alpha9
  obtain ⟨stepret9,hstep9,h⟩ := bind_success (RoundModel.step B D pre t9 ((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8) value8 9#usize) _ _ h
  have hok_tuple9 : ∃ value, stepret9 = core.result.Result.Ok value := by
    cases stepret9 with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      try dsimp (config := { zeta := true, zetaDelta := true }) only at h
      try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
      cases h
  obtain ⟨tuple9,rfl⟩ := hok_tuple9
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨value9,alpha10,t10⟩ := tuple9
  try dsimp (config := { zeta := true, zetaDelta := true }) only at h
  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok] at h
  obtain ⟨record9,q9,hr9,hs9,hset9⟩ := step_success B D pre t9 t10 ((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8) alpha10 value8 value9 9#usize 24#u8 hrow9 hstep9
  have hc9 := SemanticRoundCheckedSuccess.step_checks_of_success B D pre t9 t10 ((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8) alpha10 value8 value9 9#usize 24#u8 hrow9 hstep9
  subst alpha10
  have he := core.result.Result.Ok.inj (Result.ok.inj h)
  have ht : after = t10 := (congrArg (fun x => x.2.2) he).symm
  have ha : alpha = (((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8).set 9#usize q9) := (congrArg (fun x => x.2.1) he).symm
  have hv : running = value9 := (congrArg (fun x => x.1) he).symm
  refine ⟨initrecord, decoded_initial, initial, hinitrecord, hinitdecode, hinitindex, ?_⟩
  rw [ht, ha, hv]
  unfold schedule
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 0#usize) (row := 15#u8) (before := (initial, (Array.repeat 10#usize aspis_core.field.QM31.ZERO), self))
    (mid := (value0, ((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0), t1)) (by exact hc0) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 1#usize) (row := 16#u8) (before := (value0, ((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0), t1))
    (mid := (value1, (((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1), t2)) (by exact hc1) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 2#usize) (row := 17#u8) (before := (value1, (((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1), t2))
    (mid := (value2, ((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2), t3)) (by exact hc2) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 3#usize) (row := 18#u8) (before := (value2, ((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2), t3))
    (mid := (value3, (((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3), t4)) (by exact hc3) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 4#usize) (row := 19#u8) (before := (value3, (((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3), t4))
    (mid := (value4, ((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4), t5)) (by exact hc4) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 5#usize) (row := 20#u8) (before := (value4, ((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4), t5))
    (mid := (value5, (((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5), t6)) (by exact hc5) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 6#usize) (row := 21#u8) (before := (value5, (((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5), t6))
    (mid := (value6, ((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6), t7)) (by exact hc6) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 7#usize) (row := 22#u8) (before := (value6, ((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6), t7))
    (mid := (value7, (((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7), t8)) (by exact hc7) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 8#usize) (row := 23#u8) (before := (value7, (((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7), t8))
    (mid := (value8, ((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8), t9)) (by exact hc8) ?_
  refine CheckedRun.cons (B := B) (D := D) (pre := pre)
    (round := 9#usize) (row := 24#u8) (before := (value8, ((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8), t9))
    (mid := (value9, (((((((((((Array.repeat 10#usize aspis_core.field.QM31.ZERO).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8).set 9#usize q9), t10)) (by exact hc9) ?_
  exact CheckedRun.nil _

#print axioms rounds_checked_success
end AspisR1PublicPreparation.SemanticRoundsCheckedTrace
