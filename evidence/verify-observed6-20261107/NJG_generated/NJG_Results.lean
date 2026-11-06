import NJG_Carriers
set_option autoImplicit false
namespace AspisR1.NJG_Results
open Aeneas Aeneas.Std Result NJG_Carriers
abbrev EE := NIX_EmittedTypes.r1_wire.Error
abbrev ME := AspisR1PublicPreparation.r1_wire.Error

def upError : EE→ME
 | .Allocation=>.Allocation
 | .RowOrder a b=>.RowOrder a b
 | .InvalidRow=>.InvalidRow
 | .Tag r=>.Tag r
 | .Length r=>.Length r
 | .NonCanonical r i=>.NonCanonical r i
 | .Boundary r=>.Boundary r
 | .Terminal=>.Terminal
 | .EqualCirclePoints=>.EqualCirclePoints
 | .TrailingBytes=>.TrailingBytes
 | .Public=>.Public

def downError : ME→EE
 | .Allocation=>.Allocation
 | .RowOrder a b=>.RowOrder a b
 | .InvalidRow=>.InvalidRow
 | .Tag r=>.Tag r
 | .Length r=>.Length r
 | .NonCanonical r i=>.NonCanonical r i
 | .Boundary r=>.Boundary r
 | .Terminal=>.Terminal
 | .EqualCirclePoints=>.EqualCirclePoints
 | .TrailingBytes=>.TrailingBytes
 | .Public=>.Public

theorem error_roundtrip (e : EE) : downError (upError e)=e := by cases e <;> rfl
theorem error_back (e : ME) : upError (downError e)=e := by cases e <;> rfl

def upResult {H : Type} : Result (core.result.Result (NIX_EmittedTypes.r1_semantic.Verified H) EE) →
 Result (core.result.Result (AspisR1PublicPreparation.r1_semantic.Verified H) ME)
 | .ok (.Ok v)=>.ok (.Ok (upVerified v))
 | .ok (.Err e)=>.ok (.Err (upError e))
 | .fail e=>.fail e
 | .div=>.div

def downResult {H : Type} : Result (core.result.Result (AspisR1PublicPreparation.r1_semantic.Verified H) ME) →
 Result (core.result.Result (NIX_EmittedTypes.r1_semantic.Verified H) EE)
 | .ok (.Ok v)=>.ok (.Ok (downVerified v))
 | .ok (.Err e)=>.ok (.Err (downError e))
 | .fail e=>.fail e
 | .div=>.div

/-- A bijective carrier map loses neither errors, aborts, divergence nor any
Verified field. This is nominal transport only, not the open op9 equation. -/
theorem result_roundtrip {H : Type}
 (r : Result (core.result.Result (NIX_EmittedTypes.r1_semantic.Verified H) EE)) :
 downResult (upResult r)=r := by
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>cases r <;> simp only [upResult,downResult,verified_roundtrip,error_roundtrip]

theorem result_injective {H : Type}
 (a b : Result (core.result.Result (NIX_EmittedTypes.r1_semantic.Verified H) EE))
 (same : upResult a=upResult b) : a=b := by
 have h:=congrArg downResult same
 simpa only [result_roundtrip] using h

#print axioms error_roundtrip
#print axioms error_back
#print axioms result_roundtrip
#print axioms result_injective
end AspisR1.NJG_Results
