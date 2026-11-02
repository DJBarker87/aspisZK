import PV_EVH_EntropyDeployedLayout
import PV_EVH_EntropyMoveBacking
set_option autoImplicit false
namespace PV_EVH_EntropyReturnLayout
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (sameKey)
open PV_EVH_EntropyDeployedLayout (original field seed entered)
open PV_EVH_StackRegions (Separate)

/-- Actual caller Result fields at1,33,65. Preserve the transferred source
owner key; the ABI pointer and Result layout binding remain FRAME-ENTRY/V370. -/
def returnedField (owner sp result : Nat) (w : State) : Slot :=
  {field owner sp w with address := result+33}

def returnedSeed (owner sp result : Nat) (w : State) : Slot :=
  {seed owner sp w with address := result+65}

/-- Initialized caller return footprint vs callee reservation, the exact remaining invocation
boundary. No convenient numeric return address is chosen. -/
def CallerSeparate (sp result : Nat) : Prop := result+97 ≤ sp ∨ sp+232 ≤ result

theorem backing_frames (owner sp result : Nat) (w : State)
    (h : CallerSeparate sp result) :
    Separate (returnedSeed owner sp result w) (returnedField owner sp result w) ∧
    Separate (returnedField owner sp result w) (seed owner sp w) ∧
    Separate (original owner sp w) (returnedField owner sp result w) ∧
    Separate (original owner sp w) (returnedSeed owner sp result w) := by
  change (result+65+32 ≤ result+33 ∨ result+33+32 ≤ result+65) ∧
    (result+33+32 ≤ sp+96 ∨ sp+96+32 ≤ result+33) ∧
    (sp+64 ≤ result+33 ∨ result+33+32 ≤ sp) ∧
    (sp+64 ≤ result+65 ∨ result+65+32 ≤ sp)
  unfold CallerSeparate at h
  omega

/-- Existing returned backing survives original64 cleanup. Four per-field
FRAME inputs are discharged from the actual caller/callee layout boundary.
This remains the pair relocation representation: all96-byte Self move,
Result tag, staging slots and L3 observations are NOT claimed installed. -/
theorem returned_backing (owner sp result : Nat) (w : State)
    (h : CallerSeparate sp result) (i : Nat) (hi : i < 32) :
    let v := PV_EVH_StackZero.drop (original owner sp w)
      (PV_EVH_EntropyMoveBacking.pair (field owner sp w) (seed owner sp w)
        (returnedField owner sp result w) (returnedSeed owner sp result w) w)
    v.memory (result+33+i) = w.memory (sp+64+i) ∧
      v.memory (result+65+i) = w.memory (sp+96+i) := by
  have hf := backing_frames owner sp result w h
  exact PV_EVH_EntropyMoveBacking.returned_backing (field owner sp w)
    (seed owner sp w) (returnedField owner sp result w)
    (returnedSeed owner sp result w) (original owner sp w) w
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 i hi hi hi

#print axioms backing_frames
#print axioms returned_backing
end PV_EVH_EntropyReturnLayout
