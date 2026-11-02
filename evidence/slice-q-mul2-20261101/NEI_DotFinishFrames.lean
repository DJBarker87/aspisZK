import NEI_EbyFinishAssociation
import NEI_ReduceRefLaw
set_option autoImplicit false
noncomputable section
namespace NEI_DotFinishFrames
open Aeneas Aeneas.Std Result
def run {A S Event : Type} (state : S) (result : Result A) : Result (A × S × List Event) := do
 let value ← result;ok (value,state,[])
theorem reduce {S Event : Type} (state : S) (x : U64) :
 run (Event:=Event) state (NEI_DotFinishRaw.fast_pairing.canonical.reduce x) =
 run (Event:=Event) state (FIo_Native.fast_pairing.canonical.reduce x) := by
 rw [NEI_DotReduction.same]
theorem dot {S Event : Type} (state : S) (x : NEI_DotFinishAssociation.D) :
 run (Event:=Event) state (NEI_DotFinishRaw.fast_pairing.canonical.Dot.finish x) =
 run (Event:=Event) state (FIo_Native.fast_pairing.canonical.Dot.finish (NEI_DotFinishAssociation.toD x)) := by
 rw [NEI_DotFinishAssociation.finish]
theorem limbs {S Event : Type} (state : S) (x : NEI_DotFinishRaw.fast_pairing.canonical.Q) :
 run (Event:=Event) state (NEI_DotFinishRaw.fast_pairing.canonical.Q.limbs x) =
 run (Event:=Event) state (FIo_Native.fast_pairing.canonical.Q.limbs x) := by
 rw [NEI_DotFinishAssociation.limbs]
theorem outer {S Event : Type} (state : S) (x : NEI_DotFinishRaw.fast_pairing.EbyKDot) :
 run (Event:=Event) state (do let out ← NEI_DotFinishRaw.fast_pairing.EbyKDot.finish x;ok (NEI_EbyFinishAssociation.toE out)) =
 run (Event:=Event) state (FIo_Native.fast_pairing.EbyKDot.finish (NEI_EbyFinishAssociation.toOuter x)) := by
 rw [NEI_EbyFinishAssociation.same]
#print axioms reduce
#print axioms dot
#print axioms limbs
#print axioms outer
end NEI_DotFinishFrames
end
