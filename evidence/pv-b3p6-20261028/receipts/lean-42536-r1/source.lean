import PV_B3P_BytesV3Emission226
import PV_B3P_ByteOutput226
namespace PV_B3P_EncodeTag226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
set_option maxRecDepth 2048

theorem tag (p : reference226.OwnedPublic) (chunks : PV_B3P_ByteOutput226.Chunks)
    (n : Usize) (h : reference226.encode_owned p = .ok (.Ok (chunks,n))) :
    n = if p.withdrawal then 1427#usize else 1455#usize := by
  unfold reference226.encode_owned at h
  cases hp : p.withdrawal with
  | false =>
    have hu : { p with withdrawal := false } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu] at h
    generalize hr0 : reference226.chunk p 0#usize = r0 at h
    cases r0 with
    | fail e => cases h
    | div => cases h
    | ok inner =>
      cases inner with
      | Err e => cases h
      | Ok c0 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        generalize hr1 : reference226.chunk p 64#usize = r1 at h
        cases r1 with
        | fail e => cases h
        | div => cases h
        | ok inner =>
          cases inner with
          | Err e => cases h
          | Ok c1 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            generalize hr2 : reference226.chunk p 128#usize = r2 at h
            cases r2 with
            | fail e => cases h
            | div => cases h
            | ok inner =>
              cases inner with
              | Err e => cases h
              | Ok c2 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                generalize hr3 : reference226.chunk p 192#usize = r3 at h
                cases r3 with
                | fail e => cases h
                | div => cases h
                | ok inner =>
                  cases inner with
                  | Err e => cases h
                  | Ok c3 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                    generalize hr4 : reference226.chunk p 256#usize = r4 at h
                    cases r4 with
                    | fail e => cases h
                    | div => cases h
                    | ok inner =>
                      cases inner with
                      | Err e => cases h
                      | Ok c4 =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                        generalize hr5 : reference226.chunk p 320#usize = r5 at h
                        cases r5 with
                        | fail e => cases h
                        | div => cases h
                        | ok inner =>
                          cases inner with
                          | Err e => cases h
                          | Ok c5 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                            generalize hr6 : reference226.chunk p 384#usize = r6 at h
                            cases r6 with
                            | fail e => cases h
                            | div => cases h
                            | ok inner =>
                              cases inner with
                              | Err e => cases h
                              | Ok c6 =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                generalize hr7 : reference226.chunk p 448#usize = r7 at h
                                cases r7 with
                                | fail e => cases h
                                | div => cases h
                                | ok inner =>
                                  cases inner with
                                  | Err e => cases h
                                  | Ok c7 =>
                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                    generalize hr8 : reference226.chunk p 512#usize = r8 at h
                                    cases r8 with
                                    | fail e => cases h
                                    | div => cases h
                                    | ok inner =>
                                      cases inner with
                                      | Err e => cases h
                                      | Ok c8 =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                        generalize hr9 : reference226.chunk p 576#usize = r9 at h
                                        cases r9 with
                                        | fail e => cases h
                                        | div => cases h
                                        | ok inner =>
                                          cases inner with
                                          | Err e => cases h
                                          | Ok c9 =>
                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                            generalize hr10 : reference226.chunk p 640#usize = r10 at h
                                            cases r10 with
                                            | fail e => cases h
                                            | div => cases h
                                            | ok inner =>
                                              cases inner with
                                              | Err e => cases h
                                              | Ok c10 =>
                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                generalize hr11 : reference226.chunk p 704#usize = r11 at h
                                                cases r11 with
                                                | fail e => cases h
                                                | div => cases h
                                                | ok inner =>
                                                  cases inner with
                                                  | Err e => cases h
                                                  | Ok c11 =>
                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                    generalize hr12 : reference226.chunk p 768#usize = r12 at h
                                                    cases r12 with
                                                    | fail e => cases h
                                                    | div => cases h
                                                    | ok inner =>
                                                      cases inner with
                                                      | Err e => cases h
                                                      | Ok c12 =>
                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                        generalize hr13 : reference226.chunk p 832#usize = r13 at h
                                                        cases r13 with
                                                        | fail e => cases h
                                                        | div => cases h
                                                        | ok inner =>
                                                          cases inner with
                                                          | Err e => cases h
                                                          | Ok c13 =>
                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                            generalize hr14 : reference226.chunk p 896#usize = r14 at h
                                                            cases r14 with
                                                            | fail e => cases h
                                                            | div => cases h
                                                            | ok inner =>
                                                              cases inner with
                                                              | Err e => cases h
                                                              | Ok c14 =>
                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                generalize hr15 : reference226.chunk p 960#usize = r15 at h
                                                                cases r15 with
                                                                | fail e => cases h
                                                                | div => cases h
                                                                | ok inner =>
                                                                  cases inner with
                                                                  | Err e => cases h
                                                                  | Ok c15 =>
                                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                    generalize hr16 : reference226.chunk p 1024#usize = r16 at h
                                                                    cases r16 with
                                                                    | fail e => cases h
                                                                    | div => cases h
                                                                    | ok inner =>
                                                                      cases inner with
                                                                      | Err e => cases h
                                                                      | Ok c16 =>
                                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                        generalize hr17 : reference226.chunk p 1088#usize = r17 at h
                                                                        cases r17 with
                                                                        | fail e => cases h
                                                                        | div => cases h
                                                                        | ok inner =>
                                                                          cases inner with
                                                                          | Err e => cases h
                                                                          | Ok c17 =>
                                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                            generalize hr18 : reference226.chunk p 1152#usize = r18 at h
                                                                            cases r18 with
                                                                            | fail e => cases h
                                                                            | div => cases h
                                                                            | ok inner =>
                                                                              cases inner with
                                                                              | Err e => cases h
                                                                              | Ok c18 =>
                                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                generalize hr19 : reference226.chunk p 1216#usize = r19 at h
                                                                                cases r19 with
                                                                                | fail e => cases h
                                                                                | div => cases h
                                                                                | ok inner =>
                                                                                  cases inner with
                                                                                  | Err e => cases h
                                                                                  | Ok c19 =>
                                                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                    generalize hr20 : reference226.chunk p 1280#usize = r20 at h
                                                                                    cases r20 with
                                                                                    | fail e => cases h
                                                                                    | div => cases h
                                                                                    | ok inner =>
                                                                                      cases inner with
                                                                                      | Err e => cases h
                                                                                      | Ok c20 =>
                                                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                        generalize hr21 : reference226.chunk p 1344#usize = r21 at h
                                                                                        cases r21 with
                                                                                        | fail e => cases h
                                                                                        | div => cases h
                                                                                        | ok inner =>
                                                                                          cases inner with
                                                                                          | Err e => cases h
                                                                                          | Ok c21 =>
                                                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                            generalize hr22 : reference226.chunk p 1408#usize = r22 at h
                                                                                            cases r22 with
                                                                                            | fail e => cases h
                                                                                            | div => cases h
                                                                                            | ok inner =>
                                                                                              cases inner with
                                                                                              | Err e => cases h
                                                                                              | Ok c22 =>
                                                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                                cases h
                                                                                                rfl
  | true =>
    have hu : { p with withdrawal := true } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu] at h
    generalize hr0 : reference226.chunk p 0#usize = r0 at h
    cases r0 with
    | fail e => cases h
    | div => cases h
    | ok inner =>
      cases inner with
      | Err e => cases h
      | Ok c0 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        generalize hr1 : reference226.chunk p 64#usize = r1 at h
        cases r1 with
        | fail e => cases h
        | div => cases h
        | ok inner =>
          cases inner with
          | Err e => cases h
          | Ok c1 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            generalize hr2 : reference226.chunk p 128#usize = r2 at h
            cases r2 with
            | fail e => cases h
            | div => cases h
            | ok inner =>
              cases inner with
              | Err e => cases h
              | Ok c2 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                generalize hr3 : reference226.chunk p 192#usize = r3 at h
                cases r3 with
                | fail e => cases h
                | div => cases h
                | ok inner =>
                  cases inner with
                  | Err e => cases h
                  | Ok c3 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                    generalize hr4 : reference226.chunk p 256#usize = r4 at h
                    cases r4 with
                    | fail e => cases h
                    | div => cases h
                    | ok inner =>
                      cases inner with
                      | Err e => cases h
                      | Ok c4 =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                        generalize hr5 : reference226.chunk p 320#usize = r5 at h
                        cases r5 with
                        | fail e => cases h
                        | div => cases h
                        | ok inner =>
                          cases inner with
                          | Err e => cases h
                          | Ok c5 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                            generalize hr6 : reference226.chunk p 384#usize = r6 at h
                            cases r6 with
                            | fail e => cases h
                            | div => cases h
                            | ok inner =>
                              cases inner with
                              | Err e => cases h
                              | Ok c6 =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                generalize hr7 : reference226.chunk p 448#usize = r7 at h
                                cases r7 with
                                | fail e => cases h
                                | div => cases h
                                | ok inner =>
                                  cases inner with
                                  | Err e => cases h
                                  | Ok c7 =>
                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                    generalize hr8 : reference226.chunk p 512#usize = r8 at h
                                    cases r8 with
                                    | fail e => cases h
                                    | div => cases h
                                    | ok inner =>
                                      cases inner with
                                      | Err e => cases h
                                      | Ok c8 =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                        generalize hr9 : reference226.chunk p 576#usize = r9 at h
                                        cases r9 with
                                        | fail e => cases h
                                        | div => cases h
                                        | ok inner =>
                                          cases inner with
                                          | Err e => cases h
                                          | Ok c9 =>
                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                            generalize hr10 : reference226.chunk p 640#usize = r10 at h
                                            cases r10 with
                                            | fail e => cases h
                                            | div => cases h
                                            | ok inner =>
                                              cases inner with
                                              | Err e => cases h
                                              | Ok c10 =>
                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                generalize hr11 : reference226.chunk p 704#usize = r11 at h
                                                cases r11 with
                                                | fail e => cases h
                                                | div => cases h
                                                | ok inner =>
                                                  cases inner with
                                                  | Err e => cases h
                                                  | Ok c11 =>
                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                    generalize hr12 : reference226.chunk p 768#usize = r12 at h
                                                    cases r12 with
                                                    | fail e => cases h
                                                    | div => cases h
                                                    | ok inner =>
                                                      cases inner with
                                                      | Err e => cases h
                                                      | Ok c12 =>
                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                        generalize hr13 : reference226.chunk p 832#usize = r13 at h
                                                        cases r13 with
                                                        | fail e => cases h
                                                        | div => cases h
                                                        | ok inner =>
                                                          cases inner with
                                                          | Err e => cases h
                                                          | Ok c13 =>
                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                            generalize hr14 : reference226.chunk p 896#usize = r14 at h
                                                            cases r14 with
                                                            | fail e => cases h
                                                            | div => cases h
                                                            | ok inner =>
                                                              cases inner with
                                                              | Err e => cases h
                                                              | Ok c14 =>
                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                generalize hr15 : reference226.chunk p 960#usize = r15 at h
                                                                cases r15 with
                                                                | fail e => cases h
                                                                | div => cases h
                                                                | ok inner =>
                                                                  cases inner with
                                                                  | Err e => cases h
                                                                  | Ok c15 =>
                                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                    generalize hr16 : reference226.chunk p 1024#usize = r16 at h
                                                                    cases r16 with
                                                                    | fail e => cases h
                                                                    | div => cases h
                                                                    | ok inner =>
                                                                      cases inner with
                                                                      | Err e => cases h
                                                                      | Ok c16 =>
                                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                        generalize hr17 : reference226.chunk p 1088#usize = r17 at h
                                                                        cases r17 with
                                                                        | fail e => cases h
                                                                        | div => cases h
                                                                        | ok inner =>
                                                                          cases inner with
                                                                          | Err e => cases h
                                                                          | Ok c17 =>
                                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                            generalize hr18 : reference226.chunk p 1152#usize = r18 at h
                                                                            cases r18 with
                                                                            | fail e => cases h
                                                                            | div => cases h
                                                                            | ok inner =>
                                                                              cases inner with
                                                                              | Err e => cases h
                                                                              | Ok c18 =>
                                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                generalize hr19 : reference226.chunk p 1216#usize = r19 at h
                                                                                cases r19 with
                                                                                | fail e => cases h
                                                                                | div => cases h
                                                                                | ok inner =>
                                                                                  cases inner with
                                                                                  | Err e => cases h
                                                                                  | Ok c19 =>
                                                                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                    generalize hr20 : reference226.chunk p 1280#usize = r20 at h
                                                                                    cases r20 with
                                                                                    | fail e => cases h
                                                                                    | div => cases h
                                                                                    | ok inner =>
                                                                                      cases inner with
                                                                                      | Err e => cases h
                                                                                      | Ok c20 =>
                                                                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                        generalize hr21 : reference226.chunk p 1344#usize = r21 at h
                                                                                        cases r21 with
                                                                                        | fail e => cases h
                                                                                        | div => cases h
                                                                                        | ok inner =>
                                                                                          cases inner with
                                                                                          | Err e => cases h
                                                                                          | Ok c21 =>
                                                                                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                            generalize hr22 : reference226.chunk p 1408#usize = r22 at h
                                                                                            cases r22 with
                                                                                            | fail e => cases h
                                                                                            | div => cases h
                                                                                            | ok inner =>
                                                                                              cases inner with
                                                                                              | Err e => cases h
                                                                                              | Ok c22 =>
                                                                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                                                                                                cases h
                                                                                                rfl

#print axioms tag
end PV_B3P_EncodeTag226V3
