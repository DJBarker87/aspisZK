import KND_Composition
import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KND_LPm_K004
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (source : Nat → Nat) (len cap next j : Nat) (limit : len≤1704)
 (live : len≤cap) (growth : cap≤next) (bound : j<len+32) :
 len+32≤1736 ∧ window source (loop before garbage 0 (min cap next)) len 32 j =
 (if j<len then before j else source (j-len)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source len cap next 32 j live growth bound
theorem conditional_writer (step : KND_Schedule.Step → KND_Composition.State → KND_Composition.State → KND_Composition.State)
 (value : String → KND_Composition.State) (before : KND_Composition.State)
 (valid : ∀ s ∈ KND_Schedule.schedule, ∀ b v, step s b v = KND_Composition.model s b v) :
 KND_Composition.execute step value KND_Schedule.schedule before =
 KND_Composition.execute KND_Composition.model value KND_Schedule.schedule before :=
 KND_Composition.schedule_composition step value before valid
#print axioms result
#print axioms conditional_writer
def applicable : List KND_Schedule.Step := [⟨"proof_digest",16,1768,32⟩,⟨"public_digest",48,1768,32⟩,⟨"state",80,1768,32⟩,⟨"root0",112,1768,32⟩,⟨"root1",144,1768,32⟩,⟨"gamma",176,1768,32⟩,⟨"kappa",208,1768,32⟩,⟨"alpha0",240,1768,32⟩,⟨"alpha1",272,1768,32⟩,⟨"claim",632,1768,32⟩,⟨"rhs",664,1768,32⟩,⟨"checksum",1736,1768,32⟩]
theorem reachable : ∀ s ∈ applicable, s ∈ KND_Schedule.schedule := by decide
theorem no_growth : ∀ s ∈ applicable, s.len+s.size≤s.cap := by decide
#print axioms reachable
#print axioms no_growth
end KND_LPm_K004
