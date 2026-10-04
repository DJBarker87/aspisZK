import AspisV8R19.R646CombineLoopExecution
import AspisV8R19.R638CombineAcceptedInputs
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R663CombineWrapperExecution

open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta
open AspisV8R19.R646CombineLoopExecution

private abbrev U4 := Fin 4

/-- The actual selected `combine_beta` wrapper composes the two successful
fixed-width decoders with the actual four-slot loop. The decoder and leaf
execution facts remain explicit premises. -/
theorem combine_beta_wrapper_execution
    (c1 c2 : Slice U8)
    (powers : query_arithmetic.BetaCoefficients)
    (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (lane : U4 → U4 → U32)
    (h1 : query_arithmetic.r55_decode_into c1
      (Array.repeat 104#usize 0#u32) =
        .ok (core.result.Result.Ok (), a1))
    (h2 : query_arithmetic.r55_decode_into c2
      (Array.repeat 48#usize 0#u32) =
        .ok (core.result.Result.Ok (), a2))
    (hleaf : ∀ (slot : U4) (limb : U4),
      query_arithmetic.r83_mixed_limb (UScalar.ofNatCore limb.val
        (by have h := Usize.cMax_bound; scalar_tac))
        (c1Chunk a1 slot) a2 (sourceIndex slot) powers = .ok (lane slot limb)) :
    query_arithmetic.combine_beta c1 c2 powers =
      .ok (core.result.Result.Ok (laneArray lane)) := by
  unfold query_arithmetic.combine_beta
  rw [h1]
  simp only [bind_tc_ok]
  rw [h2]
  simp only [bind_tc_ok]
  rw [AspisR614SelectedCombineBeta.combine_beta_loop_four
    powers a1 a2 lane hleaf]
  rfl

#print axioms combine_beta_wrapper_execution

end AspisV8R19.R663CombineWrapperExecution
