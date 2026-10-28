import PV_B3P_ByteChunk226
import PV_B3P_RustResult
namespace PV_B3P_ChunkLaw226
open Aeneas Aeneas.Std PV_B3P_226 PV_B3P_RustResult
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error
-- All four outer/inner Result cases are preserved by every bind.
def spec (p : reference226.OwnedPublic) (base : Usize) :
    Result (core.result.Result (Array U8 64#usize) E) :=
  bindR (reference226.byte_at p (Usize.wrapping_add base 0#usize)) (fun v0 =>
    bindR (reference226.byte_at p (Usize.wrapping_add base 1#usize)) (fun v1 =>
      bindR (reference226.byte_at p (Usize.wrapping_add base 2#usize)) (fun v2 =>
        bindR (reference226.byte_at p (Usize.wrapping_add base 3#usize)) (fun v3 =>
          bindR (reference226.byte_at p (Usize.wrapping_add base 4#usize)) (fun v4 =>
            bindR (reference226.byte_at p (Usize.wrapping_add base 5#usize)) (fun v5 =>
              bindR (reference226.byte_at p (Usize.wrapping_add base 6#usize)) (fun v6 =>
                bindR (reference226.byte_at p (Usize.wrapping_add base 7#usize)) (fun v7 =>
                  bindR (reference226.byte_at p (Usize.wrapping_add base 8#usize)) (fun v8 =>
                    bindR (reference226.byte_at p (Usize.wrapping_add base 9#usize)) (fun v9 =>
                      bindR (reference226.byte_at p (Usize.wrapping_add base 10#usize)) (fun v10 =>
                        bindR (reference226.byte_at p (Usize.wrapping_add base 11#usize)) (fun v11 =>
                          bindR (reference226.byte_at p (Usize.wrapping_add base 12#usize)) (fun v12 =>
                            bindR (reference226.byte_at p (Usize.wrapping_add base 13#usize)) (fun v13 =>
                              bindR (reference226.byte_at p (Usize.wrapping_add base 14#usize)) (fun v14 =>
                                bindR (reference226.byte_at p (Usize.wrapping_add base 15#usize)) (fun v15 =>
                                  bindR (reference226.byte_at p (Usize.wrapping_add base 16#usize)) (fun v16 =>
                                    bindR (reference226.byte_at p (Usize.wrapping_add base 17#usize)) (fun v17 =>
                                      bindR (reference226.byte_at p (Usize.wrapping_add base 18#usize)) (fun v18 =>
                                        bindR (reference226.byte_at p (Usize.wrapping_add base 19#usize)) (fun v19 =>
                                          bindR (reference226.byte_at p (Usize.wrapping_add base 20#usize)) (fun v20 =>
                                            bindR (reference226.byte_at p (Usize.wrapping_add base 21#usize)) (fun v21 =>
                                              bindR (reference226.byte_at p (Usize.wrapping_add base 22#usize)) (fun v22 =>
                                                bindR (reference226.byte_at p (Usize.wrapping_add base 23#usize)) (fun v23 =>
                                                  bindR (reference226.byte_at p (Usize.wrapping_add base 24#usize)) (fun v24 =>
                                                    bindR (reference226.byte_at p (Usize.wrapping_add base 25#usize)) (fun v25 =>
                                                      bindR (reference226.byte_at p (Usize.wrapping_add base 26#usize)) (fun v26 =>
                                                        bindR (reference226.byte_at p (Usize.wrapping_add base 27#usize)) (fun v27 =>
                                                          bindR (reference226.byte_at p (Usize.wrapping_add base 28#usize)) (fun v28 =>
                                                            bindR (reference226.byte_at p (Usize.wrapping_add base 29#usize)) (fun v29 =>
                                                              bindR (reference226.byte_at p (Usize.wrapping_add base 30#usize)) (fun v30 =>
                                                                bindR (reference226.byte_at p (Usize.wrapping_add base 31#usize)) (fun v31 =>
                                                                  bindR (reference226.byte_at p (Usize.wrapping_add base 32#usize)) (fun v32 =>
                                                                    bindR (reference226.byte_at p (Usize.wrapping_add base 33#usize)) (fun v33 =>
                                                                      bindR (reference226.byte_at p (Usize.wrapping_add base 34#usize)) (fun v34 =>
                                                                        bindR (reference226.byte_at p (Usize.wrapping_add base 35#usize)) (fun v35 =>
                                                                          bindR (reference226.byte_at p (Usize.wrapping_add base 36#usize)) (fun v36 =>
                                                                            bindR (reference226.byte_at p (Usize.wrapping_add base 37#usize)) (fun v37 =>
                                                                              bindR (reference226.byte_at p (Usize.wrapping_add base 38#usize)) (fun v38 =>
                                                                                bindR (reference226.byte_at p (Usize.wrapping_add base 39#usize)) (fun v39 =>
                                                                                  bindR (reference226.byte_at p (Usize.wrapping_add base 40#usize)) (fun v40 =>
                                                                                    bindR (reference226.byte_at p (Usize.wrapping_add base 41#usize)) (fun v41 =>
                                                                                      bindR (reference226.byte_at p (Usize.wrapping_add base 42#usize)) (fun v42 =>
                                                                                        bindR (reference226.byte_at p (Usize.wrapping_add base 43#usize)) (fun v43 =>
                                                                                          bindR (reference226.byte_at p (Usize.wrapping_add base 44#usize)) (fun v44 =>
                                                                                            bindR (reference226.byte_at p (Usize.wrapping_add base 45#usize)) (fun v45 =>
                                                                                              bindR (reference226.byte_at p (Usize.wrapping_add base 46#usize)) (fun v46 =>
                                                                                                bindR (reference226.byte_at p (Usize.wrapping_add base 47#usize)) (fun v47 =>
                                                                                                  bindR (reference226.byte_at p (Usize.wrapping_add base 48#usize)) (fun v48 =>
                                                                                                    bindR (reference226.byte_at p (Usize.wrapping_add base 49#usize)) (fun v49 =>
                                                                                                      bindR (reference226.byte_at p (Usize.wrapping_add base 50#usize)) (fun v50 =>
                                                                                                        bindR (reference226.byte_at p (Usize.wrapping_add base 51#usize)) (fun v51 =>
                                                                                                          bindR (reference226.byte_at p (Usize.wrapping_add base 52#usize)) (fun v52 =>
                                                                                                            bindR (reference226.byte_at p (Usize.wrapping_add base 53#usize)) (fun v53 =>
                                                                                                              bindR (reference226.byte_at p (Usize.wrapping_add base 54#usize)) (fun v54 =>
                                                                                                                bindR (reference226.byte_at p (Usize.wrapping_add base 55#usize)) (fun v55 =>
                                                                                                                  bindR (reference226.byte_at p (Usize.wrapping_add base 56#usize)) (fun v56 =>
                                                                                                                    bindR (reference226.byte_at p (Usize.wrapping_add base 57#usize)) (fun v57 =>
                                                                                                                      bindR (reference226.byte_at p (Usize.wrapping_add base 58#usize)) (fun v58 =>
                                                                                                                        bindR (reference226.byte_at p (Usize.wrapping_add base 59#usize)) (fun v59 =>
                                                                                                                          bindR (reference226.byte_at p (Usize.wrapping_add base 60#usize)) (fun v60 =>
                                                                                                                            bindR (reference226.byte_at p (Usize.wrapping_add base 61#usize)) (fun v61 =>
                                                                                                                              bindR (reference226.byte_at p (Usize.wrapping_add base 62#usize)) (fun v62 =>
                                                                                                                                bindR (reference226.byte_at p (Usize.wrapping_add base 63#usize)) (fun v63 =>
                                                                                                                                  .ok (.Ok (Array.make 64#usize [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63] (by rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem complete_result (p : reference226.OwnedPublic) (base : Usize) :
    reference226.chunk p base = spec p base := by
  unfold reference226.chunk spec
  simp only [try_bind_eq]

#print axioms complete_result
end PV_B3P_ChunkLaw226
