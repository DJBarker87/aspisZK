import PV_B3P_BytesV3Emission226
import PV_B3P_RustResult
namespace PV_B3P_EncodeLaw226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
abbrev E := aspis_core.state_only_prefix.r0.Error
def spec (p : reference226.OwnedPublic) :
    Result (core.result.Result ((Array (Array U8 64#usize) 23#usize) × Usize) E) :=
  bindR (reference226.chunk p 0#usize) (fun v0 =>
    bindR (reference226.chunk p 64#usize) (fun v1 =>
      bindR (reference226.chunk p 128#usize) (fun v2 =>
        bindR (reference226.chunk p 192#usize) (fun v3 =>
          bindR (reference226.chunk p 256#usize) (fun v4 =>
            bindR (reference226.chunk p 320#usize) (fun v5 =>
              bindR (reference226.chunk p 384#usize) (fun v6 =>
                bindR (reference226.chunk p 448#usize) (fun v7 =>
                  bindR (reference226.chunk p 512#usize) (fun v8 =>
                    bindR (reference226.chunk p 576#usize) (fun v9 =>
                      bindR (reference226.chunk p 640#usize) (fun v10 =>
                        bindR (reference226.chunk p 704#usize) (fun v11 =>
                          bindR (reference226.chunk p 768#usize) (fun v12 =>
                            bindR (reference226.chunk p 832#usize) (fun v13 =>
                              bindR (reference226.chunk p 896#usize) (fun v14 =>
                                bindR (reference226.chunk p 960#usize) (fun v15 =>
                                  bindR (reference226.chunk p 1024#usize) (fun v16 =>
                                    bindR (reference226.chunk p 1088#usize) (fun v17 =>
                                      bindR (reference226.chunk p 1152#usize) (fun v18 =>
                                        bindR (reference226.chunk p 1216#usize) (fun v19 =>
                                          bindR (reference226.chunk p 1280#usize) (fun v20 =>
                                            bindR (reference226.chunk p 1344#usize) (fun v21 =>
                                              bindR (reference226.chunk p 1408#usize) (fun v22 =>
                                                .ok (.Ok (Array.make 23#usize [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22] (by rfl), if p.withdrawal then 1427#usize else 1455#usize)))))))))))))))))))))))))
set_option backward.isDefEq.respectTransparency false in
theorem complete_result (p : reference226.OwnedPublic) :
    reference226.encode_owned p = spec p := by
  unfold reference226.encode_owned spec
  cases hw : p.withdrawal
  all_goals
    have hu : { p with withdrawal := p.withdrawal } = p := by cases p; rfl
    simp only [hw] at hu
    simp only [hw,Bool.false_eq_true,↓reduceIte,bind_tc_ok] 
    rw [hu]
    generalize h0 : reference226.chunk p 0#usize = r0
    cases r0 with
    | fail e => rfl
    | div => rfl
    | ok v =>
      cases v with
      | Err e => rfl
      | Ok v0 =>
        generalize h1 : reference226.chunk p 64#usize = r1
        cases r1 with
        | fail e => rfl
        | div => rfl
        | ok v =>
          cases v with
          | Err e => rfl
          | Ok v1 =>
            generalize h2 : reference226.chunk p 128#usize = r2
            cases r2 with
            | fail e => rfl
            | div => rfl
            | ok v =>
              cases v with
              | Err e => rfl
              | Ok v2 =>
                generalize h3 : reference226.chunk p 192#usize = r3
                cases r3 with
                | fail e => rfl
                | div => rfl
                | ok v =>
                  cases v with
                  | Err e => rfl
                  | Ok v3 =>
                    generalize h4 : reference226.chunk p 256#usize = r4
                    cases r4 with
                    | fail e => rfl
                    | div => rfl
                    | ok v =>
                      cases v with
                      | Err e => rfl
                      | Ok v4 =>
                        generalize h5 : reference226.chunk p 320#usize = r5
                        cases r5 with
                        | fail e => rfl
                        | div => rfl
                        | ok v =>
                          cases v with
                          | Err e => rfl
                          | Ok v5 =>
                            generalize h6 : reference226.chunk p 384#usize = r6
                            cases r6 with
                            | fail e => rfl
                            | div => rfl
                            | ok v =>
                              cases v with
                              | Err e => rfl
                              | Ok v6 =>
                                generalize h7 : reference226.chunk p 448#usize = r7
                                cases r7 with
                                | fail e => rfl
                                | div => rfl
                                | ok v =>
                                  cases v with
                                  | Err e => rfl
                                  | Ok v7 =>
                                    generalize h8 : reference226.chunk p 512#usize = r8
                                    cases r8 with
                                    | fail e => rfl
                                    | div => rfl
                                    | ok v =>
                                      cases v with
                                      | Err e => rfl
                                      | Ok v8 =>
                                        generalize h9 : reference226.chunk p 576#usize = r9
                                        cases r9 with
                                        | fail e => rfl
                                        | div => rfl
                                        | ok v =>
                                          cases v with
                                          | Err e => rfl
                                          | Ok v9 =>
                                            generalize h10 : reference226.chunk p 640#usize = r10
                                            cases r10 with
                                            | fail e => rfl
                                            | div => rfl
                                            | ok v =>
                                              cases v with
                                              | Err e => rfl
                                              | Ok v10 =>
                                                generalize h11 : reference226.chunk p 704#usize = r11
                                                cases r11 with
                                                | fail e => rfl
                                                | div => rfl
                                                | ok v =>
                                                  cases v with
                                                  | Err e => rfl
                                                  | Ok v11 =>
                                                    generalize h12 : reference226.chunk p 768#usize = r12
                                                    cases r12 with
                                                    | fail e => rfl
                                                    | div => rfl
                                                    | ok v =>
                                                      cases v with
                                                      | Err e => rfl
                                                      | Ok v12 =>
                                                        generalize h13 : reference226.chunk p 832#usize = r13
                                                        cases r13 with
                                                        | fail e => rfl
                                                        | div => rfl
                                                        | ok v =>
                                                          cases v with
                                                          | Err e => rfl
                                                          | Ok v13 =>
                                                            generalize h14 : reference226.chunk p 896#usize = r14
                                                            cases r14 with
                                                            | fail e => rfl
                                                            | div => rfl
                                                            | ok v =>
                                                              cases v with
                                                              | Err e => rfl
                                                              | Ok v14 =>
                                                                generalize h15 : reference226.chunk p 960#usize = r15
                                                                cases r15 with
                                                                | fail e => rfl
                                                                | div => rfl
                                                                | ok v =>
                                                                  cases v with
                                                                  | Err e => rfl
                                                                  | Ok v15 =>
                                                                    generalize h16 : reference226.chunk p 1024#usize = r16
                                                                    cases r16 with
                                                                    | fail e => rfl
                                                                    | div => rfl
                                                                    | ok v =>
                                                                      cases v with
                                                                      | Err e => rfl
                                                                      | Ok v16 =>
                                                                        generalize h17 : reference226.chunk p 1088#usize = r17
                                                                        cases r17 with
                                                                        | fail e => rfl
                                                                        | div => rfl
                                                                        | ok v =>
                                                                          cases v with
                                                                          | Err e => rfl
                                                                          | Ok v17 =>
                                                                            generalize h18 : reference226.chunk p 1152#usize = r18
                                                                            cases r18 with
                                                                            | fail e => rfl
                                                                            | div => rfl
                                                                            | ok v =>
                                                                              cases v with
                                                                              | Err e => rfl
                                                                              | Ok v18 =>
                                                                                generalize h19 : reference226.chunk p 1216#usize = r19
                                                                                cases r19 with
                                                                                | fail e => rfl
                                                                                | div => rfl
                                                                                | ok v =>
                                                                                  cases v with
                                                                                  | Err e => rfl
                                                                                  | Ok v19 =>
                                                                                    generalize h20 : reference226.chunk p 1280#usize = r20
                                                                                    cases r20 with
                                                                                    | fail e => rfl
                                                                                    | div => rfl
                                                                                    | ok v =>
                                                                                      cases v with
                                                                                      | Err e => rfl
                                                                                      | Ok v20 =>
                                                                                        generalize h21 : reference226.chunk p 1344#usize = r21
                                                                                        cases r21 with
                                                                                        | fail e => rfl
                                                                                        | div => rfl
                                                                                        | ok v =>
                                                                                          cases v with
                                                                                          | Err e => rfl
                                                                                          | Ok v21 =>
                                                                                            generalize h22 : reference226.chunk p 1408#usize = r22
                                                                                            cases r22 with
                                                                                            | fail e => rfl
                                                                                            | div => rfl
                                                                                            | ok v =>
                                                                                              cases v with
                                                                                              | Err e => rfl
                                                                                              | Ok v22 =>
                                                                                                rfl
#print axioms complete_result
end PV_B3P_EncodeLaw226
