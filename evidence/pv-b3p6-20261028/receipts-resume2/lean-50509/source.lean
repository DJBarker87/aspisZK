import PV_B3P_BytesV3Emission226
import PV_B3P_RustResult
import PV_B3P_Repeat226
import PV_B3P_ArrayEight226
namespace PV_B3P_Chunk64Law226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8
abbrev E := aspis_core.state_only_prefix.r0.Error
def join (xs : List (Array U8 8#usize)) (h : xs.length = 8) : Array U8 64#usize :=
  Array.make 64#usize (xs.flatMap (fun x => x.val)) (by
    have hh : ∀ ys : List (Array U8 8#usize), (ys.flatMap (fun x => x.val)).length = ys.length * 8 := by
      intro ys
      induction ys with
      | nil => rfl
      | cons y ys ih => simp only [List.flatMap_cons,List.length_append,y.property,List.length_cons,ih]; omega
    rw [hh,h]; rfl)
def spec (p : reference226.OwnedPublic) (base : Usize) : Result (core.result.Result (Array U8 64#usize) E) :=
  bindR (reference226.chunk8 p (Usize.wrapping_add base 0#usize)) (fun v0 =>
    bindR (reference226.chunk8 p (Usize.wrapping_add base 8#usize)) (fun v1 =>
      bindR (reference226.chunk8 p (Usize.wrapping_add base 16#usize)) (fun v2 =>
        bindR (reference226.chunk8 p (Usize.wrapping_add base 24#usize)) (fun v3 =>
          bindR (reference226.chunk8 p (Usize.wrapping_add base 32#usize)) (fun v4 =>
            bindR (reference226.chunk8 p (Usize.wrapping_add base 40#usize)) (fun v5 =>
              bindR (reference226.chunk8 p (Usize.wrapping_add base 48#usize)) (fun v6 =>
                bindR (reference226.chunk8 p (Usize.wrapping_add base 56#usize)) (fun v7 =>
                  .ok (.Ok (join [v0,v1,v2,v3,v4,v5,v6,v7] (by rfl)))))))))))
set_option backward.isDefEq.respectTransparency false in
theorem complete_result (p : reference226.OwnedPublic) (base : Usize) :
    reference226.chunk p base = spec p base := by
  unfold reference226.chunk spec
  simp only [lift,bind_tc_ok]
  generalize h0 : reference226.chunk8 p (Usize.wrapping_add base 0#usize) = r0
  cases r0 with
  | fail e => rfl
  | div => rfl
  | ok v =>
    cases v with
    | Err e => rfl
    | Ok v0 =>
      generalize h1 : reference226.chunk8 p (Usize.wrapping_add base 8#usize) = r1
      cases r1 with
      | fail e => rfl
      | div => rfl
      | ok v =>
        cases v with
        | Err e => rfl
        | Ok v1 =>
          generalize h2 : reference226.chunk8 p (Usize.wrapping_add base 16#usize) = r2
          cases r2 with
          | fail e => rfl
          | div => rfl
          | ok v =>
            cases v with
            | Err e => rfl
            | Ok v2 =>
              generalize h3 : reference226.chunk8 p (Usize.wrapping_add base 24#usize) = r3
              cases r3 with
              | fail e => rfl
              | div => rfl
              | ok v =>
                cases v with
                | Err e => rfl
                | Ok v3 =>
                  generalize h4 : reference226.chunk8 p (Usize.wrapping_add base 32#usize) = r4
                  cases r4 with
                  | fail e => rfl
                  | div => rfl
                  | ok v =>
                    cases v with
                    | Err e => rfl
                    | Ok v4 =>
                      generalize h5 : reference226.chunk8 p (Usize.wrapping_add base 40#usize) = r5
                      cases r5 with
                      | fail e => rfl
                      | div => rfl
                      | ok v =>
                        cases v with
                        | Err e => rfl
                        | Ok v5 =>
                          generalize h6 : reference226.chunk8 p (Usize.wrapping_add base 48#usize) = r6
                          cases r6 with
                          | fail e => rfl
                          | div => rfl
                          | ok v =>
                            cases v with
                            | Err e => rfl
                            | Ok v6 =>
                              generalize h7 : reference226.chunk8 p (Usize.wrapping_add base 56#usize) = r7
                              cases r7 with
                              | fail e => rfl
                              | div => rfl
                              | ok v =>
                                cases v with
                                | Err e => rfl
                                | Ok v7 =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v0 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v1 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v2 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v3 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v4 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v5 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v6 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 0#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 1#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 2#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 3#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 4#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 5#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 6#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  rw [PV_B3P_Repeat226.index_value v7 7#usize (by decide)]
                                  simp only [bind_tc_ok]
                                  apply congrArg (fun a => Result.ok (core.result.Result.Ok a))
                                  apply Subtype.ext
                                  change _ = ([v0,v1,v2,v3,v4,v5,v6,v7].flatMap (fun a => a.val))
                                  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,← PV_B3P_ArrayEight226.values]
                                  rfl
#print axioms complete_result
end PV_B3P_Chunk64Law226
