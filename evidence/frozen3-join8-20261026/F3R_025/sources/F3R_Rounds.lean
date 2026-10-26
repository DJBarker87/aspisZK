import F3R_RoundState
import F3R_Pure
import S1SemanticCodeRoundsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Rounds
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.roundStep

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (B : RoundModel.Boundaries)
    (c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 : SourceFull25.Call D pre)
    (row15 : c15.row=15#u8)
    (row16 : c16.row=16#u8)
    (row17 : c17.row=17#u8)
    (row18 : c18.row=18#u8)
    (row19 : c19.row=19#u8)
    (row20 : c20.row=20#u8)
    (row21 : c21.row=21#u8)
    (row22 : c22.row=22#u8)
    (row23 : c23.row=23#u8)
    (row24 : c24.row=24#u8)
    (same16 : c16.before=c15.after)
    (same17 : c17.before=c16.after)
    (same18 : c18.before=c17.after)
    (same19 : c19.before=c18.after)
    (same20 : c20.before=c19.after)
    (same21 : c21.before=c20.after)
    (same22 : c22.before=c21.after)
    (same23 : c23.before=c22.after)
    (same24 : c24.before=c23.after)
    (out : aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript Hash)
    (success : erase (S1SemanticCode.rounds B D pre c15.before)=ok (.Ok out)) :
    observe (run (S1SemanticCode.rounds B D pre c15.before)).1=
      callLog c15++callLog c16++callLog c17++callLog c18++callLog c19++callLog c20++callLog c21++callLog c22++callLog c23++callLog c24 := by
  unfold S1SemanticCode.rounds at success ⊢
  obtain ⟨recordResult,hrecord,s0,l0⟩ := F3Q_PreparePure.right _ _ _ success
  rw [l0]
  cases recordResult with
  | Err e =>
    simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at s0
    cases s0
  | Ok record =>
    erw [F3R_Pure.erase_ok] at s0
    erw [F3K_CodeStep.pure_step]
    obtain ⟨decodedResult,hdecoded,s1,l1⟩ := F3Q_PreparePure.right _ _ _ s0
    rw [l1]
    cases decodedResult with
    | Err e =>
      simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at s1
      cases s1
    | Ok polynomial =>
      erw [F3R_Pure.erase_ok] at s1
      erw [F3K_CodeStep.pure_step]
      obtain ⟨running,hrunning,s2,l2⟩ := F3Q_PreparePure.right _ _ _ s1
      rw [l2]
      obtain ⟨result0,call0,s3,l3⟩ := AuS1_Trace.success_bind _ _ _ s2
      rw [l3,AuS1_Trace.observe_append]
      cases result0 with
      | Err e =>
        simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at s3
        cases s3
      | Ok value0 =>
        have bound0 : c15.row.val<25 := by rw [row15];decide
        have tag0 : 15#u8+UScalar.cast .U8 0#usize=ok c15.row := by rw [row15];rfl
        rw [F3R_RoundStep.log B c15 bound0 _ _ _ tag0 _ call0]
        erw [F3R_Pure.erase_ok] at s3
        erw [F3K_CodeStep.pure_step]
        have state0 := F3R_RoundState.state B c15 _ _ _ tag0 _ call0
        try simp only at s3 ⊢
        rw [state0,← same16] at s3 ⊢
        obtain ⟨result1,call1,s4,l4⟩ := AuS1_Trace.success_bind _ _ _ s3
        rw [l4,AuS1_Trace.observe_append]
        cases result1 with
        | Err e =>
          simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at s4
          cases s4
        | Ok value1 =>
          have bound1 : c16.row.val<25 := by rw [row16];decide
          have tag1 : 15#u8+UScalar.cast .U8 1#usize=ok c16.row := by rw [row16];rfl
          rw [F3R_RoundStep.log B c16 bound1 _ _ _ tag1 _ call1]
          erw [F3R_Pure.erase_ok] at s4
          erw [F3K_CodeStep.pure_step]
          have state1 := F3R_RoundState.state B c16 _ _ _ tag1 _ call1
          try simp only at s4 ⊢
          rw [state1,← same17] at s4 ⊢
          obtain ⟨result2,call2,s5,l5⟩ := AuS1_Trace.success_bind _ _ _ s4
          rw [l5,AuS1_Trace.observe_append]
          cases result2 with
          | Err e =>
            simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at s5
            cases s5
          | Ok value2 =>
            have bound2 : c17.row.val<25 := by rw [row17];decide
            have tag2 : 15#u8+UScalar.cast .U8 2#usize=ok c17.row := by rw [row17];rfl
            rw [F3R_RoundStep.log B c17 bound2 _ _ _ tag2 _ call2]
            erw [F3R_Pure.erase_ok] at s5
            erw [F3K_CodeStep.pure_step]
            have state2 := F3R_RoundState.state B c17 _ _ _ tag2 _ call2
            try simp only at s5 ⊢
            rw [state2,← same18] at s5 ⊢
            obtain ⟨result3,call3,s6,l6⟩ := AuS1_Trace.success_bind _ _ _ s5
            rw [l6,AuS1_Trace.observe_append]
            cases result3 with
            | Err e =>
              simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at s6
              cases s6
            | Ok value3 =>
              have bound3 : c18.row.val<25 := by rw [row18];decide
              have tag3 : 15#u8+UScalar.cast .U8 3#usize=ok c18.row := by rw [row18];rfl
              rw [F3R_RoundStep.log B c18 bound3 _ _ _ tag3 _ call3]
              erw [F3R_Pure.erase_ok] at s6
              erw [F3K_CodeStep.pure_step]
              have state3 := F3R_RoundState.state B c18 _ _ _ tag3 _ call3
              try simp only at s6 ⊢
              rw [state3,← same19] at s6 ⊢
              obtain ⟨result4,call4,s7,l7⟩ := AuS1_Trace.success_bind _ _ _ s6
              rw [l7,AuS1_Trace.observe_append]
              cases result4 with
              | Err e =>
                simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at s7
                cases s7
              | Ok value4 =>
                have bound4 : c19.row.val<25 := by rw [row19];decide
                have tag4 : 15#u8+UScalar.cast .U8 4#usize=ok c19.row := by rw [row19];rfl
                rw [F3R_RoundStep.log B c19 bound4 _ _ _ tag4 _ call4]
                erw [F3R_Pure.erase_ok] at s7
                erw [F3K_CodeStep.pure_step]
                have state4 := F3R_RoundState.state B c19 _ _ _ tag4 _ call4
                try simp only at s7 ⊢
                rw [state4,← same20] at s7 ⊢
                obtain ⟨result5,call5,s8,l8⟩ := AuS1_Trace.success_bind _ _ _ s7
                rw [l8,AuS1_Trace.observe_append]
                cases result5 with
                | Err e =>
                  simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at s8
                  cases s8
                | Ok value5 =>
                  have bound5 : c20.row.val<25 := by rw [row20];decide
                  have tag5 : 15#u8+UScalar.cast .U8 5#usize=ok c20.row := by rw [row20];rfl
                  rw [F3R_RoundStep.log B c20 bound5 _ _ _ tag5 _ call5]
                  erw [F3R_Pure.erase_ok] at s8
                  erw [F3K_CodeStep.pure_step]
                  have state5 := F3R_RoundState.state B c20 _ _ _ tag5 _ call5
                  try simp only at s8 ⊢
                  rw [state5,← same21] at s8 ⊢
                  obtain ⟨result6,call6,s9,l9⟩ := AuS1_Trace.success_bind _ _ _ s8
                  rw [l9,AuS1_Trace.observe_append]
                  cases result6 with
                  | Err e =>
                    simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at s9
                    cases s9
                  | Ok value6 =>
                    have bound6 : c21.row.val<25 := by rw [row21];decide
                    have tag6 : 15#u8+UScalar.cast .U8 6#usize=ok c21.row := by rw [row21];rfl
                    rw [F3R_RoundStep.log B c21 bound6 _ _ _ tag6 _ call6]
                    erw [F3R_Pure.erase_ok] at s9
                    erw [F3K_CodeStep.pure_step]
                    have state6 := F3R_RoundState.state B c21 _ _ _ tag6 _ call6
                    try simp only at s9 ⊢
                    rw [state6,← same22] at s9 ⊢
                    obtain ⟨result7,call7,s10,l10⟩ := AuS1_Trace.success_bind _ _ _ s9
                    rw [l10,AuS1_Trace.observe_append]
                    cases result7 with
                    | Err e =>
                      simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at s10
                      cases s10
                    | Ok value7 =>
                      have bound7 : c22.row.val<25 := by rw [row22];decide
                      have tag7 : 15#u8+UScalar.cast .U8 7#usize=ok c22.row := by rw [row22];rfl
                      rw [F3R_RoundStep.log B c22 bound7 _ _ _ tag7 _ call7]
                      erw [F3R_Pure.erase_ok] at s10
                      erw [F3K_CodeStep.pure_step]
                      have state7 := F3R_RoundState.state B c22 _ _ _ tag7 _ call7
                      try simp only at s10 ⊢
                      rw [state7,← same23] at s10 ⊢
                      obtain ⟨result8,call8,s11,l11⟩ := AuS1_Trace.success_bind _ _ _ s10
                      rw [l11,AuS1_Trace.observe_append]
                      cases result8 with
                      | Err e =>
                        simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at s11
                        cases s11
                      | Ok value8 =>
                        have bound8 : c23.row.val<25 := by rw [row23];decide
                        have tag8 : 15#u8+UScalar.cast .U8 8#usize=ok c23.row := by rw [row23];rfl
                        rw [F3R_RoundStep.log B c23 bound8 _ _ _ tag8 _ call8]
                        erw [F3R_Pure.erase_ok] at s11
                        erw [F3K_CodeStep.pure_step]
                        have state8 := F3R_RoundState.state B c23 _ _ _ tag8 _ call8
                        try simp only at s11 ⊢
                        rw [state8,← same24] at s11 ⊢
                        obtain ⟨result9,call9,s12,l12⟩ := AuS1_Trace.success_bind _ _ _ s11
                        rw [l12,AuS1_Trace.observe_append]
                        cases result9 with
                        | Err e =>
                          simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at s12
                          cases s12
                        | Ok value9 =>
                          have bound9 : c24.row.val<25 := by rw [row24];decide
                          have tag9 : 15#u8+UScalar.cast .U8 9#usize=ok c24.row := by rw [row24];rfl
                          rw [F3R_RoundStep.log B c24 bound9 _ _ _ tag9 _ call9]
                          erw [F3R_Pure.erase_ok] at s12
                          erw [F3K_CodeStep.pure_step]
                          simp only [run,observe,List.flatMap_nil,List.append_nil,List.append_assoc]

#print axioms log
end AspisR1.F3R_Rounds
end
