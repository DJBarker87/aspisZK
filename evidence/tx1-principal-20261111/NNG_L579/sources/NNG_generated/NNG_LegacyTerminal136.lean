import NNG_LegacyCalls136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyTerminal136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
abbrev OldError := AspisR1PublicPreparation.aspis_core.state_only_prefix.r0.Error

def error : NNG_ModelTerminal.Error → OldError
 | .Allocation=>.Allocation | .RowOrder a b=>.RowOrder a b | .InvalidRow=>.InvalidRow
 | .Tag a=>.Tag a | .Length a=>.Length a | .NonCanonical a b=>.NonCanonical a b
 | .Boundary a=>.Boundary a | .Terminal=>.Terminal | .EqualCirclePoints=>.EqualCirclePoints
 | .TrailingBytes=>.TrailingBytes | .Public=>.Public

theorem error_native (e : NNG_ModelTerminal.NativeError) :
 error (NNG_ModelTerminal.raiseError e)=FIq_Terminal.fromError e := by cases e <;> rfl

theorem arguments (pub : Public) (claims : Claims) (alpha : Alpha) (challenges : aspis_core.state_only_prefix.r0.Challenges) :
 FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 (FIq_Carriers.toPublic (toT9 pub))
  (FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ) (NNG_InstallClaims.lowerClaims claims))
  (FIq_Carriers.mapArray FIq_Carriers.toQ (arr toT1 alpha)) (FIq_Carriers.toChallenges (toT3 challenges)) =
 NNG_ModelTerminal.native pub claims alpha challenges := by
 unfold NNG_ModelTerminal.native NNG_InstallClaims.lowerClaims NNG_ModelTerminal.lowerQ
 simp only [FIq_Carriers.mapArray,arr,List.map_map,Function.comp_def]
 rfl

theorem model (pub : Public) (claims : Claims) (alpha : Alpha) (challenges : aspis_core.state_only_prefix.r0.Challenges) :
 outer (NMP_ResultTransport.inner toT1 error) (NNG_ModelTerminal.call pub claims alpha challenges)=
 FIq_Terminal.terminal (toT9 pub) (NNG_InstallClaims.lowerClaims claims) (arr toT1 alpha) (toT3 challenges) := by
 unfold FIq_Terminal.terminal NNG_ModelTerminal.call
 rw [arguments]
 generalize NNG_ModelTerminal.native pub claims alpha challenges=r
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>
   cases r with
   | Err e=>simp only [outer,NMP_ResultTransport.inner,bind_tc_ok,error_native]
   | Ok q=>simp only [outer,NMP_ResultTransport.inner,bind_tc_ok,NNG_ModelTerminal.raiseQ,fromT1_inverse]
#print axioms error_native
#print axioms arguments
#print axioms model
end AspisR1.NNG_LegacyTerminal136
