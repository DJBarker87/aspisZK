import KND_Composition
import KNA_Frame
import KMZ_LPi_K018
set_option autoImplicit false
namespace KND_LPi_K018
open KMX_CopyMeaning KMY_WindowComposition
theorem result (body garbage hp hu answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 0+3=3 ∧ 1736+32=1768 ∧
 window answer (loop (KMZ_LPi_K018.joinedPrefix body hp hu) garbage 0 (min 1736 3472)) 1736 32 j =
 if 16≤j ∧ j<48 then hp (j-16) else if 48≤j ∧ j<80 then hu (j-48)
 else if j<1736 then body j else if j<1768 then answer (j-1736) else body j := by
 refine ⟨by omega,by omega,?_⟩
 exact KMZ_LPi_K018.result body garbage hp hu answer j bound
theorem conditional_writer (step : KND_Schedule.Step → KND_Composition.State → KND_Composition.State → KND_Composition.State)
 (value : String → KND_Composition.State) (before : KND_Composition.State)
 (valid : ∀ s ∈ KND_Schedule.schedule, ∀ b v, step s b v = KND_Composition.model s b v) :
 KND_Composition.execute step value KND_Schedule.schedule before =
 KND_Composition.execute KND_Composition.model value KND_Schedule.schedule before :=
 KND_Composition.schedule_composition step value before valid
#print axioms result
#print axioms conditional_writer
end KND_LPi_K018
