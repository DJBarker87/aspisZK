import NOC_Op9
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_PrepareDiv
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

/-- Finding: the host configuration never installs the current caller's
allocation slot op1; it is NNH_HostSeed.m0's divergent residual. -/
theorem op1_div {W Tx : Type} (c : Ctx W Tx) (n : Usize) (x : U8) :
 (DrvC_Installation.currentInstalled (configuration c)).op1 core.marker.CopyU8 n x = .div := rfl

theorem logical_semantic {W Tx : Type} (c : Ctx W Tx) :
 compact.LOGICAL_SEMANTIC (DrvC_Installation.currentInstalled (configuration c)) = ok 13831#usize := by
 unfold compact.LOGICAL_SEMANTIC; rfl

theorem logical_y1 : compact.LOGICAL_Y1 = ok 928#usize := by
 unfold compact.LOGICAL_Y1
 first | rfl | (apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac)

theorem logical_sum : ((13831#usize : Usize) + (928#usize : Usize)) = ok 14759#usize := by
 first | rfl | (apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac)

/-- Consequently the installed 087 prepare front diverges on EVERY input at
the host configuration, before any data-dependent step. -/
theorem prepare_div {W Tx H : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 verifier.candidate.prepare (DrvC_Installation.currentInstalled (configuration c)) D pub proof hash obs g = .div := by
 unfold verifier.candidate.prepare
 noc_stp (logical_semantic c)
 noc_stp logical_y1
 noc_stp logical_sum
 rw [op1_div]
 rfl
#print axioms op1_div
#print axioms logical_semantic
#print axioms logical_y1
#print axioms logical_sum
#print axioms prepare_div
end AspisR1.NOC_PrepareDiv
end
