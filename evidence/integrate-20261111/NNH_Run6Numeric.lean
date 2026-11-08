import NNH_Run6Host
set_option autoImplicit false
namespace AspisR1.NNH_Run6Numeric
/-- The single recorder charge is one nonnegative summand of the adopted total. -/
theorem charge_le_total (Q : Nat) : F3T_Numeric.accountLoss Q ≤ F3T_Numeric.total Q := by
 have h0 : 0 ≤ ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B + F3T_Numeric.collisionLoss Q := by
  unfold F3T_Numeric.collisionLoss PerAttemptEnvelope.B
  positivity
 have h1 : (0:Rat) ≤ 1/(2:Rat)^126 := by positivity
 have h2 : (0:Rat) ≤ 1/(2:Rat)^454 := by positivity
 unfold F3T_Numeric.total
 linarith
#print axioms charge_le_total
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run6Host
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
/-- Existing failureModel-to-total chain, on normalize a, at every actual pair. -/
theorem host_bound
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (fx : NNH_Run5bCtx.Fixed) (w : NNH_Run5bCtx.World W Tx) (H : Bytes → State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx) :
 let c := RSL.TASB.ctxB (X (Tx := Tx) L0 copy std) fx w H
 F3T_RuntimeBound.failureModel (NNH_Run5bHost.runtime L0 copy c
  ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c)) ≤
 F3T_Numeric.total (fx.Q0+fx.Q1) := by
 let c := RSL.TASB.ctxB (X (Tx := Tx) L0 copy std) fx w H
 have ext := (NNH_Run5bHost.a0 L0 copy std).extraction c
  ((X (Tx := Tx) L0 copy std).exhibited_mk _ _ _ _ _)
 have q : (S (Tx := Tx) L0 copy std).Queries c ((S (Tx := Tx) L0 copy std).model1 c) := queries H
 exact ((NNH_Run5bHeadline.headline L0 borrow copy std).numeric c _ _ ext q).1
#print axioms host_bound
end AspisR1.NNH_Run6Numeric
