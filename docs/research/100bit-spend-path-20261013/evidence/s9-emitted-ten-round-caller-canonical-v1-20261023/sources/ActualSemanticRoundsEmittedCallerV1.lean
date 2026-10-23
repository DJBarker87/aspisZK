import ActualSemanticRoundsInitialCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ActualSemanticRoundsEmittedCallerV1
open AspisR1ActualSemanticRoundCutV1
open AspisR1ActualSemanticRoundSourceModelV1
abbrev QM := AspisR1ActualSemanticRoundSourceModelV1.QM

/- Actual extracted caller body. Existing codec/round operations are uniform
Hooks, and the external constant is an arbitrary Result. No literal value,
canonicality or independent success is assumed for that constant. -/
/-- [aspis_r1_cost_probe::r1_semantic::semantic_rounds]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 133:0-179:1 -/
def emittedSemanticRounds (B : Hooks) (zeroResult : Result QM)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
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
      let q ← zeroResult
      let alpha := Array.repeat 10#usize q
      let r2 ←
        semanticRound B aspis_coredigestDigest32Inst prefix1
          transcript alpha running 0#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (running1, alpha1, transcript1) := val1
        let r3 ←
          semanticRound B aspis_coredigestDigest32Inst prefix1
            transcript1 alpha1 running1 1#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (running2, alpha2, transcript2) := val2
          let r4 ←
            semanticRound B aspis_coredigestDigest32Inst prefix1
              transcript2 alpha2 running2 2#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let (running3, alpha3, transcript3) := val3
            let r5 ←
              semanticRound B aspis_coredigestDigest32Inst prefix1
                transcript3 alpha3 running3 3#usize
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let (running4, alpha4, transcript4) := val4
              let r6 ←
                semanticRound B aspis_coredigestDigest32Inst prefix1
                  transcript4 alpha4 running4 4#usize
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let (running5, alpha5, transcript5) := val5
                let r7 ←
                  semanticRound B aspis_coredigestDigest32Inst
                    prefix1 transcript5 alpha5 running5 5#usize
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let (running6, alpha6, transcript6) := val6
                  let r8 ←
                    semanticRound B aspis_coredigestDigest32Inst
                      prefix1 transcript6 alpha6 running6 6#usize
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let (running7, alpha7, transcript7) := val7
                    let r9 ←
                      semanticRound B aspis_coredigestDigest32Inst
                        prefix1 transcript7 alpha7 running7 7#usize
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let (running8, alpha8, transcript8) := val8
                      let r10 ←
                        semanticRound B aspis_coredigestDigest32Inst
                          prefix1 transcript8 alpha8 running8 8#usize
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let (running9, alpha9, transcript9) := val9
                        let r11 ←
                          semanticRound B
                            aspis_coredigestDigest32Inst prefix1 transcript9
                            alpha9 running9 9#usize
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

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Full-result equality after the same constant call has succeeded. This is
not a claim that replacing its value preserves acceptance or oracle traces. -/
theorem emitted_ok_initial_eq_source {H : Type} (B : Hooks) (initialAlphaValue : QM)
    (D : aspis_core.digest.Digest32 H) (pre : r1_wire.Prefix)
    (self : r1_wire.SemanticTranscript H) :
    emittedSemanticRounds B (.ok initialAlphaValue) D pre self =
      AspisR1ActualSemanticRoundsInitialCanonicalV1.sourceRoundsWithInitial
        initialAlphaValue B D pre self := by
  unfold emittedSemanticRounds
    AspisR1ActualSemanticRoundsInitialCanonicalV1.sourceRoundsWithInitial
  simp only [bind_tc_ok] <;> rfl

/-- The constant success is extracted from this same whole caller execution. -/
theorem emitted_success_has_initial {H : Type} (B : Hooks) (zeroResult : Result QM)
    (D : aspis_core.digest.Digest32 H) (pre : r1_wire.Prefix)
    (self after : r1_wire.SemanticTranscript H)
    (running : QM) (alpha : Array QM 10#usize)
    (h : emittedSemanticRounds B zeroResult D pre self =
      .ok (.Ok (running,alpha,after))) :
    ∃ initialAlphaValue, zeroResult = .ok initialAlphaValue := by
  unfold emittedSemanticRounds at h
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
  obtain ⟨initialAlphaValue,hzero,_htail⟩ := bind_success zeroResult _ _ h
  exact ⟨initialAlphaValue,hzero⟩

/-- A successful emitted caller returns a final alpha array with canonical
successful reads. All ten writes use their same-run transcript challenges;
the source constant Result and its value are unrestricted. -/
theorem emitted_success_all_alpha_reads_canonical {H : Type}
    (B : Hooks) (zeroResult : Result QM)
    (D : aspis_core.digest.Digest32 H) (pre : r1_wire.Prefix)
    (self after : r1_wire.SemanticTranscript H)
    (running : QM) (alpha : Array QM 10#usize)
    (h : emittedSemanticRounds B zeroResult D pre self =
      .ok (.Ok (running,alpha,after))) :
    ∀ (i : Usize) (q : QM), Array.index_usize alpha i = .ok q →
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))) := by
  obtain ⟨initialAlphaValue,hzero⟩ := emitted_success_has_initial
    B zeroResult D pre self after running alpha h
  rw [hzero,emitted_ok_initial_eq_source] at h
  exact AspisR1ActualSemanticRoundsInitialCanonicalV1.actual_source_rounds_success_all_alpha_reads_canonical
    initialAlphaValue B D pre self after running alpha h

#print axioms emitted_ok_initial_eq_source
#print axioms emitted_success_has_initial
#print axioms emitted_success_all_alpha_reads_canonical
end AspisR1ActualSemanticRoundsEmittedCallerV1
