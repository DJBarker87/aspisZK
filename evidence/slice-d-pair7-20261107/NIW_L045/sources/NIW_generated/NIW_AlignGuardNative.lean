import NIW_AlignGuard
import NIT_RegularChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignGuardNative
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIW_AlignBoundary NIW_AlignControl

def nativeError : AspisR1Stage2.verifier.Error → FIo_Native.verifier.Error
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def nativeUnit : Reply Unit → RU
 | .Err e=>.Err (nativeError e) | .Ok _=>.Ok ()

def nativePartial : Reply Powers → RP
 | .Err e=>.Err (nativeError e) | .Ok values=>.Ok values

theorem error_roundtrip (e : AspisR1Stage2.verifier.Error) : FIo_Install.error (nativeError e)=e := by
 cases e <;> rfl

theorem unit_roundtrip (r : Reply Unit) : NIT_ErrorTransport.unitReply (nativeUnit r)=r := by
 cases r with
 | Err e=>exact congrArg core.result.Result.Err (error_roundtrip e)
 | Ok u=>cases u;rfl

theorem partial_roundtrip (r : Reply Powers) :
 NIT_ErrorTransport.unitReply (nativePartial r)=erasePartial r := by
 cases r with
 | Err e=>exact congrArg core.result.Result.Err (error_roundtrip e)
 | Ok values=>rfl

/-- Complete returning guard control on the SAME supplied replies. The tail is
an arbitrary complete Result, including fail/div; no chosen model packet. -/
theorem returning_control (shared : Bool) (address : Nat) (i slot power : Nat) (l : Log)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit) (tail : Result NR)
 (native : cut shared address i slot power l afterScratch afterParts out) :
 NIT_GuardComposition.dispatch (nativeUnit out) tail=
 NIT_GuardFrontJoin.control shared (nativeUnit l.regular)
  (nativeUnit (erasePartial l.partialReply)) (nativeUnit l.high) tail := by
 have observed := NIW_AlignGuard.from_cut shared address i slot power l afterScratch afterParts out native
 have normalized : cutSameGuard shared (NIW_AlignGuard.project shared l out)
  (NIT_ErrorTransport.unitReply (nativeUnit out)) := by
  rw [unit_roundtrip]
  exact observed
 exact NIT_GuardFrontJoin.native_control shared (NIW_AlignGuard.project shared l out)
  (nativeUnit l.regular) (nativeUnit (erasePartial l.partialReply)) (nativeUnit l.high) (nativeUnit out)
  tail (unit_roundtrip l.regular).symm (unit_roundtrip (erasePartial l.partialReply)).symm
  (unit_roundtrip l.high).symm normalized

/-- The actual observed regular error supplies the terminal constructor on the
actual post-regular Parts, including writes made before the Err. -/
theorem regular_rejected (c : Context) (shared : Bool) (address : Nat) (i slot power : Nat) (l : Log)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared address i slot power l afterScratch afterParts out)
 (e : AspisR1Stage2.verifier.Error) (observed : l.regular=.Err e) :
 out=.Err e ∧ NIT_RegularChain.After c shared l.partsReply (.Err (nativeError e))
  (ok (.Err (nativeError e))) := by
 have reply := native.2.2.2.2.2.2.1
 refine ⟨?_,.rejected (nativeError e)⟩
 simpa only [expected,observed] using reply

#print axioms error_roundtrip
#print axioms unit_roundtrip
#print axioms partial_roundtrip
#print axioms returning_control
#print axioms regular_rejected
end AspisR1.NIW_AlignGuardNative
