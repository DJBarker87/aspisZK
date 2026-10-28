import KND_Composition
import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KND_LPm_K005
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (word : Nat) (len cap next j : Nat) (limit : len≤1732)
 (live : len≤cap) (growth : cap≤next) (bound : j<len+4) :
 len+4≤1736 ∧ window (fun b => (word / 2^(8*b)) % 256) (loop before garbage 0 (min cap next)) len 4 j =
 (if j<len then before j else (word / 2^(8*(j-len))) % 256) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage (fun b => (word / 2^(8*b)) % 256) len cap next 4 j live growth bound
theorem conditional_writer (step : KND_Schedule.Step → KND_Composition.State → KND_Composition.State → KND_Composition.State)
 (value : String → KND_Composition.State) (before : KND_Composition.State)
 (valid : ∀ s ∈ KND_Schedule.schedule, ∀ b v, step s b v = KND_Composition.model s b v) :
 KND_Composition.execute step value KND_Schedule.schedule before =
 KND_Composition.execute KND_Composition.model value KND_Schedule.schedule before :=
 KND_Composition.schedule_composition step value before valid
#print axioms result
#print axioms conditional_writer
def applicable : List KND_Schedule.Step := [⟨"query0",320,1768,4⟩,⟨"query1",324,1768,4⟩,⟨"query2",328,1768,4⟩,⟨"query3",332,1768,4⟩,⟨"query4",336,1768,4⟩,⟨"query5",340,1768,4⟩,⟨"query6",344,1768,4⟩,⟨"query7",348,1768,4⟩,⟨"query8",352,1768,4⟩,⟨"query9",356,1768,4⟩,⟨"query10",360,1768,4⟩,⟨"query11",364,1768,4⟩,⟨"query12",368,1768,4⟩,⟨"query13",372,1768,4⟩,⟨"query14",376,1768,4⟩,⟨"query15",380,1768,4⟩,⟨"query16",384,1768,4⟩,⟨"query17",388,1768,4⟩,⟨"query18",392,1768,4⟩,⟨"query19",396,1768,4⟩,⟨"query20",400,1768,4⟩,⟨"query21",404,1768,4⟩]
theorem reachable : ∀ s ∈ applicable, s ∈ KND_Schedule.schedule := by decide
theorem no_growth : ∀ s ∈ applicable, s.len+s.size≤s.cap := by decide
#print axioms reachable
#print axioms no_growth
end KND_LPm_K005
