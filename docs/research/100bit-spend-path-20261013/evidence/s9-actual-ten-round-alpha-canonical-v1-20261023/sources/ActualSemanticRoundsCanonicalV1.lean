import ActualSemanticRoundSourceModelV1
import ActualSemanticValidatedSamplerCanonicalV1
import ActualSamplerDigitWholeMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ActualSemanticRoundsCanonicalV1
open AspisR1ActualSemanticRoundSourceModelV1
open AspisR1ActualSemanticRoundCutV1
abbrev QM := AspisR1ActualSemanticRoundSourceModelV1.QM
/-- The emitted source QM31::ZERO coordinates, locally retained because this
focused Funs owner omits the unrelated field constant declaration. -/
def actualZero : QM := ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def actualSourceRounds (B : Hooks)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.digest.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 14#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 1#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let running ← Array.index_usize val 0#usize
      let alpha := Array.repeat 10#usize actualZero
      let r2 ←
        semanticRound B aspis_coreDigest32Inst prefix1 transcript
          alpha running 0#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (running1, alpha1, transcript1) := val1
        let r3 ←
          semanticRound B aspis_coreDigest32Inst prefix1 transcript1
            alpha1 running1 1#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (running2, alpha2, transcript2) := val2
          let r4 ←
            semanticRound B aspis_coreDigest32Inst prefix1
              transcript2 alpha2 running2 2#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let (running3, alpha3, transcript3) := val3
            let r5 ←
              semanticRound B aspis_coreDigest32Inst prefix1
                transcript3 alpha3 running3 3#usize
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let (running4, alpha4, transcript4) := val4
              let r6 ←
                semanticRound B aspis_coreDigest32Inst prefix1
                  transcript4 alpha4 running4 4#usize
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let (running5, alpha5, transcript5) := val5
                let r7 ←
                  semanticRound B aspis_coreDigest32Inst prefix1
                    transcript5 alpha5 running5 5#usize
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let (running6, alpha6, transcript6) := val6
                  let r8 ←
                    semanticRound B aspis_coreDigest32Inst prefix1
                      transcript6 alpha6 running6 6#usize
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let (running7, alpha7, transcript7) := val7
                    let r9 ←
                      semanticRound B aspis_coreDigest32Inst prefix1
                        transcript7 alpha7 running7 7#usize
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let (running8, alpha8, transcript8) := val8
                      let r10 ←
                        semanticRound B aspis_coreDigest32Inst
                          prefix1 transcript8 alpha8 running8 8#usize
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let (running9, alpha9, transcript9) := val9
                        let r11 ←
                          semanticRound B aspis_coreDigest32Inst
                            prefix1 transcript9 alpha9 running9 9#usize
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val10 =>
                          ok (core.result.Result.Ok val10)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (aspis_core.field.QM31 × (Array
                            aspis_core.field.QM31 10#usize) ×
                            (r1_wire.SemanticTranscript H))
                            (core.convert.FromSame r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (aspis_core.field.QM31 × (Array
                          aspis_core.field.QM31 10#usize) ×
                          (r1_wire.SemanticTranscript H))
                          (core.convert.FromSame r1_wire.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                        10#usize) × (r1_wire.SemanticTranscript H))
                        (core.convert.FromSame r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                      10#usize) × (r1_wire.SemanticTranscript H))
                      (core.convert.FromSame r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                    10#usize) × (r1_wire.SemanticTranscript H))
                    (core.convert.FromSame r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                  10#usize) × (r1_wire.SemanticTranscript H))
                  (core.convert.FromSame r1_wire.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                10#usize) × (r1_wire.SemanticTranscript H))
                (core.convert.FromSame r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize)
              × (r1_wire.SemanticTranscript H)) (core.convert.FromSame
              r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
            (r1_wire.SemanticTranscript H)) (core.convert.FromSame
            r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
        (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
      (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
      residual


theorem actual_source_rounds_success_all_canonical {H : Type} (B : Hooks) (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pre : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix) (self after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H) (running : QM)
    (alpha : Array QM 10#usize)
    (h : actualSourceRounds B D pre self = ok (.Ok (running,alpha,after))) :
    ∃ q0 q1 q2 q3 q4 q5 q6 q7 q8 q9,
      alpha.val = [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9] ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q0))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q1))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q2))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q3))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q4))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q5))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q6))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q7))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q8))) ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q9))) := by
  unfold actualSourceRounds at h
  obtain ⟨initret,hinitrecord,h⟩ := bind_success (AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix.validated_record pre 14#u8) _ _ h
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
  obtain ⟨stepret0,hstep0,h⟩ := bind_success (semanticRound B D pre self (Array.repeat 10#usize actualZero) initial 0#usize) _ _ h
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
  obtain ⟨_,record0,q0,_hrow0,hr0,hs0,hset0⟩ := semantic_round_success_slots B D pre self t1 (Array.repeat 10#usize actualZero) alpha1 initial value0 0#usize hstep0
  subst alpha1
  obtain ⟨stepret1,hstep1,h⟩ := bind_success (semanticRound B D pre t1 ((Array.repeat 10#usize actualZero).set 0#usize q0) value0 1#usize) _ _ h
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
  obtain ⟨_,record1,q1,_hrow1,hr1,hs1,hset1⟩ := semantic_round_success_slots B D pre t1 t2 ((Array.repeat 10#usize actualZero).set 0#usize q0) alpha2 value0 value1 1#usize hstep1
  subst alpha2
  obtain ⟨stepret2,hstep2,h⟩ := bind_success (semanticRound B D pre t2 (((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1) value1 2#usize) _ _ h
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
  obtain ⟨_,record2,q2,_hrow2,hr2,hs2,hset2⟩ := semantic_round_success_slots B D pre t2 t3 (((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1) alpha3 value1 value2 2#usize hstep2
  subst alpha3
  obtain ⟨stepret3,hstep3,h⟩ := bind_success (semanticRound B D pre t3 ((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2) value2 3#usize) _ _ h
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
  obtain ⟨_,record3,q3,_hrow3,hr3,hs3,hset3⟩ := semantic_round_success_slots B D pre t3 t4 ((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2) alpha4 value2 value3 3#usize hstep3
  subst alpha4
  obtain ⟨stepret4,hstep4,h⟩ := bind_success (semanticRound B D pre t4 (((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3) value3 4#usize) _ _ h
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
  obtain ⟨_,record4,q4,_hrow4,hr4,hs4,hset4⟩ := semantic_round_success_slots B D pre t4 t5 (((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3) alpha5 value3 value4 4#usize hstep4
  subst alpha5
  obtain ⟨stepret5,hstep5,h⟩ := bind_success (semanticRound B D pre t5 ((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4) value4 5#usize) _ _ h
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
  obtain ⟨_,record5,q5,_hrow5,hr5,hs5,hset5⟩ := semantic_round_success_slots B D pre t5 t6 ((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4) alpha6 value4 value5 5#usize hstep5
  subst alpha6
  obtain ⟨stepret6,hstep6,h⟩ := bind_success (semanticRound B D pre t6 (((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5) value5 6#usize) _ _ h
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
  obtain ⟨_,record6,q6,_hrow6,hr6,hs6,hset6⟩ := semantic_round_success_slots B D pre t6 t7 (((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5) alpha7 value5 value6 6#usize hstep6
  subst alpha7
  obtain ⟨stepret7,hstep7,h⟩ := bind_success (semanticRound B D pre t7 ((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6) value6 7#usize) _ _ h
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
  obtain ⟨_,record7,q7,_hrow7,hr7,hs7,hset7⟩ := semantic_round_success_slots B D pre t7 t8 ((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6) alpha8 value6 value7 7#usize hstep7
  subst alpha8
  obtain ⟨stepret8,hstep8,h⟩ := bind_success (semanticRound B D pre t8 (((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7) value7 8#usize) _ _ h
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
  obtain ⟨_,record8,q8,_hrow8,hr8,hs8,hset8⟩ := semantic_round_success_slots B D pre t8 t9 (((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7) alpha9 value7 value8 8#usize hstep8
  subst alpha9
  obtain ⟨stepret9,hstep9,h⟩ := bind_success (semanticRound B D pre t9 ((((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8) value8 9#usize) _ _ h
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
  obtain ⟨_,record9,q9,_hrow9,hr9,hs9,hset9⟩ := semantic_round_success_slots B D pre t9 t10 ((((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8) alpha10 value8 value9 9#usize hstep9
  subst alpha10
  have he := core.result.Result.Ok.inj (Result.ok.inj h)
  have ha : alpha = (((((((((((Array.repeat 10#usize actualZero).set 0#usize q0).set 1#usize q1).set 2#usize q2).set 3#usize q3).set 4#usize q4).set 5#usize q5).set 6#usize q6).set 7#usize q7).set 8#usize q8).set 9#usize q9) := (congrArg (fun x => x.2.1) he).symm
  rw [ha]
  refine ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,?_,?_⟩
  · rfl
  · exact ⟨
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D self t1 record0 q0 hs0,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t1 t2 record1 q1 hs1,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t2 t3 record2 q2 hs2,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t3 t4 record3 q3 hs3,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t4 t5 record4 q4 hs4,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t5 t6 record5 q5 hs5,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t6 t7 record6 q6 hs6,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t7 t8 record7 q7 hs7,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t8 t9 record8 q8 hs8,
      AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical D t9 t10 record9 q9 hs9⟩


private theorem index_success_bound {A : Type} {N : Usize}
    (a : Array A N) (i : Usize) (q : A)
    (h : Array.index_usize a i = .ok q) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- A literal ten-cell readback lemma used to turn the ten existential
canonicality facts into the pointwise successful-index contract consumed by
constructor v3. -/
private theorem ten_reads_canonical {A : Type} (P : A → Prop)
    (a : Array A 10#usize) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : A)
    (hvalues : a.val = [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9])
    (h0 : P q0) (h1 : P q1) (h2 : P q2) (h3 : P q3) (h4 : P q4)
    (h5 : P q5) (h6 : P q6) (h7 : P q7) (h8 : P q8) (h9 : P q9) :
    ∀ (i : Usize) (q : A), Array.index_usize a i = .ok q → P q := by
  intro i q hread
  have hibound : i.val < 10 := by
    have hb := index_success_bound a i q hread
    have hten : (10#usize).val = 10 := by decide
    omega
  interval_cases hival : i.val
  all_goals
    simp_all [Array.index_usize, Array.getElem?_Usize_eq, hvalues]

/-- Same-run pointwise canonicality for all reads of the alpha array returned
by the actual ten-call sequence. -/
theorem actual_source_rounds_success_all_alpha_reads_canonical {H : Type}
    (B : Hooks) (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pre : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (self after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (running : QM) (alpha : Array QM 10#usize)
    (h : actualSourceRounds B D pre self = ok (.Ok (running,alpha,after))) :
    ∀ (i : Usize) (q : QM), Array.index_usize alpha i = .ok q →
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))) := by
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,hvalues,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ :=
    actual_source_rounds_success_all_canonical B D pre self after running alpha h
  exact ten_reads_canonical
    (fun q => AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld
          (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))))
    alpha q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 hvalues
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

#print axioms actual_source_rounds_success_all_alpha_reads_canonical

#print axioms actual_source_rounds_success_all_canonical
end AspisR1ActualSemanticRoundsCanonicalV1
