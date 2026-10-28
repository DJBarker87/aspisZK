import PV_B3P_Chunk64Outcome226V3
namespace PV_B3P_EncodeOutcome226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
set_option maxRecDepth 2048

theorem no_outer_failure (p : reference226.OwnedPublic)
    (h : ∀ j : Usize, ∃ r, reference226.byte_at p j = .ok r) :
    ∃ r, reference226.encode_owned p = .ok r := by
  obtain ⟨r0,h0⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 0#usize h
  obtain ⟨r1,h1⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 64#usize h
  obtain ⟨r2,h2⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 128#usize h
  obtain ⟨r3,h3⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 192#usize h
  obtain ⟨r4,h4⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 256#usize h
  obtain ⟨r5,h5⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 320#usize h
  obtain ⟨r6,h6⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 384#usize h
  obtain ⟨r7,h7⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 448#usize h
  obtain ⟨r8,h8⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 512#usize h
  obtain ⟨r9,h9⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 576#usize h
  obtain ⟨r10,h10⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 640#usize h
  obtain ⟨r11,h11⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 704#usize h
  obtain ⟨r12,h12⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 768#usize h
  obtain ⟨r13,h13⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 832#usize h
  obtain ⟨r14,h14⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 896#usize h
  obtain ⟨r15,h15⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 960#usize h
  obtain ⟨r16,h16⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1024#usize h
  obtain ⟨r17,h17⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1088#usize h
  obtain ⟨r18,h18⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1152#usize h
  obtain ⟨r19,h19⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1216#usize h
  obtain ⟨r20,h20⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1280#usize h
  obtain ⟨r21,h21⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1344#usize h
  obtain ⟨r22,h22⟩ := PV_B3P_Chunk64Outcome226V3.no_outer_failure p 1408#usize h
  unfold reference226.encode_owned
  cases hp : p.withdrawal with
  | false =>
    have hu : { p with withdrawal := false } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu]
    rw [h0]
    cases r0 with
    | Err e => exact ⟨.Err e,rfl⟩
    | Ok c0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      rw [h1]
      cases r1 with
      | Err e => exact ⟨.Err e,rfl⟩
      | Ok c1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        rw [h2]
        cases r2 with
        | Err e => exact ⟨.Err e,rfl⟩
        | Ok c2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          rw [h3]
          cases r3 with
          | Err e => exact ⟨.Err e,rfl⟩
          | Ok c3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            rw [h4]
            cases r4 with
            | Err e => exact ⟨.Err e,rfl⟩
            | Ok c4 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
              rw [h5]
              cases r5 with
              | Err e => exact ⟨.Err e,rfl⟩
              | Ok c5 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                rw [h6]
                cases r6 with
                | Err e => exact ⟨.Err e,rfl⟩
                | Ok c6 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                  rw [h7]
                  cases r7 with
                  | Err e => exact ⟨.Err e,rfl⟩
                  | Ok c7 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                    rw [h8]
                    cases r8 with
                    | Err e => exact ⟨.Err e,rfl⟩
                    | Ok c8 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                      rw [h9]
                      cases r9 with
                      | Err e => exact ⟨.Err e,rfl⟩
                      | Ok c9 =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                        rw [h10]
                        cases r10 with
                        | Err e => exact ⟨.Err e,rfl⟩
                        | Ok c10 =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                          rw [h11]
                          cases r11 with
                          | Err e => exact ⟨.Err e,rfl⟩
                          | Ok c11 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                            rw [h12]
                            cases r12 with
                            | Err e => exact ⟨.Err e,rfl⟩
                            | Ok c12 =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                              rw [h13]
                              cases r13 with
                              | Err e => exact ⟨.Err e,rfl⟩
                              | Ok c13 =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                rw [h14]
                                cases r14 with
                                | Err e => exact ⟨.Err e,rfl⟩
                                | Ok c14 =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  rw [h15]
                                  cases r15 with
                                  | Err e => exact ⟨.Err e,rfl⟩
                                  | Ok c15 =>
                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                    rw [h16]
                                    cases r16 with
                                    | Err e => exact ⟨.Err e,rfl⟩
                                    | Ok c16 =>
                                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                      rw [h17]
                                      cases r17 with
                                      | Err e => exact ⟨.Err e,rfl⟩
                                      | Ok c17 =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                        rw [h18]
                                        cases r18 with
                                        | Err e => exact ⟨.Err e,rfl⟩
                                        | Ok c18 =>
                                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                          rw [h19]
                                          cases r19 with
                                          | Err e => exact ⟨.Err e,rfl⟩
                                          | Ok c19 =>
                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                            rw [h20]
                                            cases r20 with
                                            | Err e => exact ⟨.Err e,rfl⟩
                                            | Ok c20 =>
                                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                              rw [h21]
                                              cases r21 with
                                              | Err e => exact ⟨.Err e,rfl⟩
                                              | Ok c21 =>
                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                rw [h22]
                                                cases r22 with
                                                | Err e => exact ⟨.Err e,rfl⟩
                                                | Ok c22 =>
                                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                  exact ⟨_,rfl⟩
  | true =>
    have hu : { p with withdrawal := true } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu]
    rw [h0]
    cases r0 with
    | Err e => exact ⟨.Err e,rfl⟩
    | Ok c0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      rw [h1]
      cases r1 with
      | Err e => exact ⟨.Err e,rfl⟩
      | Ok c1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        rw [h2]
        cases r2 with
        | Err e => exact ⟨.Err e,rfl⟩
        | Ok c2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          rw [h3]
          cases r3 with
          | Err e => exact ⟨.Err e,rfl⟩
          | Ok c3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            rw [h4]
            cases r4 with
            | Err e => exact ⟨.Err e,rfl⟩
            | Ok c4 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
              rw [h5]
              cases r5 with
              | Err e => exact ⟨.Err e,rfl⟩
              | Ok c5 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                rw [h6]
                cases r6 with
                | Err e => exact ⟨.Err e,rfl⟩
                | Ok c6 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                  rw [h7]
                  cases r7 with
                  | Err e => exact ⟨.Err e,rfl⟩
                  | Ok c7 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                    rw [h8]
                    cases r8 with
                    | Err e => exact ⟨.Err e,rfl⟩
                    | Ok c8 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                      rw [h9]
                      cases r9 with
                      | Err e => exact ⟨.Err e,rfl⟩
                      | Ok c9 =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                        rw [h10]
                        cases r10 with
                        | Err e => exact ⟨.Err e,rfl⟩
                        | Ok c10 =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                          rw [h11]
                          cases r11 with
                          | Err e => exact ⟨.Err e,rfl⟩
                          | Ok c11 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                            rw [h12]
                            cases r12 with
                            | Err e => exact ⟨.Err e,rfl⟩
                            | Ok c12 =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                              rw [h13]
                              cases r13 with
                              | Err e => exact ⟨.Err e,rfl⟩
                              | Ok c13 =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                rw [h14]
                                cases r14 with
                                | Err e => exact ⟨.Err e,rfl⟩
                                | Ok c14 =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  rw [h15]
                                  cases r15 with
                                  | Err e => exact ⟨.Err e,rfl⟩
                                  | Ok c15 =>
                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                    rw [h16]
                                    cases r16 with
                                    | Err e => exact ⟨.Err e,rfl⟩
                                    | Ok c16 =>
                                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                      rw [h17]
                                      cases r17 with
                                      | Err e => exact ⟨.Err e,rfl⟩
                                      | Ok c17 =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                        rw [h18]
                                        cases r18 with
                                        | Err e => exact ⟨.Err e,rfl⟩
                                        | Ok c18 =>
                                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                          rw [h19]
                                          cases r19 with
                                          | Err e => exact ⟨.Err e,rfl⟩
                                          | Ok c19 =>
                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                            rw [h20]
                                            cases r20 with
                                            | Err e => exact ⟨.Err e,rfl⟩
                                            | Ok c20 =>
                                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                              rw [h21]
                                              cases r21 with
                                              | Err e => exact ⟨.Err e,rfl⟩
                                              | Ok c21 =>
                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                rw [h22]
                                                cases r22 with
                                                | Err e => exact ⟨.Err e,rfl⟩
                                                | Ok c22 =>
                                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                  exact ⟨_,rfl⟩

#print axioms no_outer_failure
end PV_B3P_EncodeOutcome226V3
