import PV_EVH_EntropyReturnLayout
set_option autoImplicit false
namespace PV_EVH_EntropyCallerLayout
open PV_EVH_StackZero (State)

/-- At the identified retry_attempt call site, call pushes 8 bytes, the
callee saves six registers, then reserves 232. V370 retains interpretation
of this equation at reached invocations, including stack nonwrapping. -/
def caller (sp : Nat) : Nat := sp+288
def result (sp : Nat) : Nat := caller sp+64
def mask (sp : Nat) : Nat := caller sp+16

/-- No independent return/callee separation hypothesis remains at this call.
This is initialized-footprint arithmetic, not the Result ABI allocation size. -/
theorem caller_separate (sp : Nat) :
    PV_EVH_EntropyReturnLayout.CallerSeparate sp (result sp) := by
  unfold PV_EVH_EntropyReturnLayout.CallerSeparate result caller
  omega

theorem footprints (sp : Nat) :
    sp+232 ≤ mask sp ∧ mask sp+32 ≤ result sp ∧
    result sp+97 ≤ caller sp+264 := by
  unfold mask result caller
  omega

theorem mask_outside (sp i : Nat) :
    PV_EVH_EntropyDeployedLayout.OutsideFrame sp (mask sp+i) := by
  unfold PV_EVH_EntropyDeployedLayout.OutsideFrame mask caller
  omega

/-- Runtime validity of the reached caller reservation entails every callee
and initialized return byte bound. It is not inferred from assembly alone. -/
theorem bounds (sp : Nat) (h : caller sp+264 ≤ 2^64) :
    sp+232 ≤ 2^64 ∧ result sp+97 ≤ 2^64 ∧ mask sp+32 ≤ 2^64 := by
  simp only [result,mask,caller] at *
  omega

theorem returned_backing (owner sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    let v := PV_EVH_StackZero.drop (PV_EVH_EntropyDeployedLayout.original owner sp w)
      (PV_EVH_EntropyMoveBacking.pair (PV_EVH_EntropyDeployedLayout.field owner sp w)
        (PV_EVH_EntropyDeployedLayout.seed owner sp w)
        (PV_EVH_EntropyReturnLayout.returnedField owner sp (result sp) w)
        (PV_EVH_EntropyReturnLayout.returnedSeed owner sp (result sp) w) w)
    v.memory (result sp+33+i) = w.memory (sp+64+i) ∧
      v.memory (result sp+65+i) = w.memory (sp+96+i) :=
  PV_EVH_EntropyReturnLayout.returned_backing owner sp (result sp) w
    (caller_separate sp) i hi

#print axioms caller_separate
#print axioms footprints
#print axioms mask_outside
#print axioms bounds
#print axioms returned_backing
end PV_EVH_EntropyCallerLayout
