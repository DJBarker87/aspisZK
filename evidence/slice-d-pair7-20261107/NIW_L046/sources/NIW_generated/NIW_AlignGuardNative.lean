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

/-- Partial rejection is reached from observed call count, not a successful
regular-child premise. The native error identity and real post-regular Parts
are retained in the Partial constructor. -/
theorem partial_rejected (c : Context) (shared : Bool) (address : Nat) (i slot power : Nat) (l : Log)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared address i slot power l afterScratch afterParts out)
 (reached : 3≤l.count) (e : AspisR1Stage2.verifier.Error) (observed : l.partialReply=.Err e) :
 out=.Err e ∧ NIT_SharedChain.Partial c c.w l.partsReply (.Err (nativeError e))
  (ok (.Err (nativeError e))) := by
 have guard := NIW_AlignGuard.from_cut shared address i slot power l afterScratch afterParts out native
 have bound : 3≤(NIW_AlignGuard.project shared l out).count := by
  change 3≤l.count + (if out=.Ok () then 1 else 0)
  split <;> omega
 obtain ⟨sameShared,regular⟩ := NIW_AlignPair.partial_reached shared _ out guard bound
 change l.regular=.Ok () at regular
 have reply := native.2.2.2.2.2.2.1
 refine ⟨?_,.rejected (nativeError e)⟩
 simpa only [expected,regular,sameShared,ite_true,observed] using reply

/-- High rejection keeps the actual post-high Parts, including writes before
Err. Earlier success follows from entered-call reachability. -/
theorem high_rejected (c : Context) (shared : Bool) (address : Nat) (i slot power : Nat) (l : Log)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared address i slot power l afterScratch afterParts out)
 (reached : 4≤l.count) (e : AspisR1Stage2.verifier.Error) (observed : l.high=.Err e) :
 out=.Err e ∧ NIT_SharedChain.High c c.w afterParts (.Err (nativeError e))
  (ok (.Err (nativeError e))) := by
 have guard := NIW_AlignGuard.from_cut shared address i slot power l afterScratch afterParts out native
 have bound : 4≤(NIW_AlignGuard.project shared l out).count := by
  change 4≤l.count + (if out=.Ok () then 1 else 0)
  split <;> omega
 obtain ⟨sameShared,regular,partials⟩ := NIW_AlignPair.high_reached shared _ out guard bound
 change l.regular=.Ok () at regular
 change erasePartial l.partialReply=.Ok () at partials
 have values : ∃ values,l.partialReply=.Ok values := by
  cases result : l.partialReply with
  | Err e=>simp [erasePartial,result] at partials
  | Ok values=>exact ⟨values,rfl⟩
 obtain ⟨values,partialReply⟩ := values
 have reply := native.2.2.2.2.2.2.1
 refine ⟨?_,.rejected (nativeError e)⟩
 simpa only [expected,regular,sameShared,ite_true,partialReply] using reply

#print axioms partial_rejected
#print axioms high_rejected

#print axioms error_roundtrip
#print axioms unit_roundtrip
#print axioms partial_roundtrip
#print axioms returning_control
#print axioms regular_rejected
end AspisR1.NIW_AlignGuardNative
