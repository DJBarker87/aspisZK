import PV_B3P_BytesV3Emission226
import PV_B3P_RustResult
namespace PV_B3P_ChunkV3Law226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def spec8 (p : reference226.OwnedPublic) (base : Usize) :
    Result (core.result.Result (Array U8 8#usize) E) :=
  bindR (reference226.byte_at p (Usize.wrapping_add base 0#usize)) (fun v0 =>
    bindR (reference226.byte_at p (Usize.wrapping_add base 1#usize)) (fun v1 =>
      bindR (reference226.byte_at p (Usize.wrapping_add base 2#usize)) (fun v2 =>
        bindR (reference226.byte_at p (Usize.wrapping_add base 3#usize)) (fun v3 =>
          bindR (reference226.byte_at p (Usize.wrapping_add base 4#usize)) (fun v4 =>
            bindR (reference226.byte_at p (Usize.wrapping_add base 5#usize)) (fun v5 =>
              bindR (reference226.byte_at p (Usize.wrapping_add base 6#usize)) (fun v6 =>
                bindR (reference226.byte_at p (Usize.wrapping_add base 7#usize)) (fun v7 =>
                  .ok (.Ok (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7] (by rfl)))))))))))
theorem complete_result (p : reference226.OwnedPublic) (base : Usize) :
    reference226.chunk8 p base = spec8 p base := by
  unfold reference226.chunk8 spec8
  simp only [try_bind_eq]

#print axioms complete_result
end PV_B3P_ChunkV3Law226
