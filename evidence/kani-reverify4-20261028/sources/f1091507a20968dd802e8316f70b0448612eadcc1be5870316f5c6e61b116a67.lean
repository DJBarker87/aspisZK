import KND_Composition
import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KND_LPi_K012
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (limb : Nat → Nat) (len cap next j : Nat) (limit : len≤1720)
 (live : len≤cap) (growth : cap≤next) (bound : j<len+16) :
 len+16≤1736 ∧ window (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) (loop before garbage 0 (min cap next)) len 16 j =
 (if j<len then before j else (limb ((j-len)/4) / 2^(8*((j-len)%4))) % 256) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) len cap next 16 j live growth bound
theorem conditional_writer (step : KND_Schedule.Step → KND_Composition.State → KND_Composition.State → KND_Composition.State)
 (value : String → KND_Composition.State) (before : KND_Composition.State)
 (valid : ∀ s ∈ KND_Schedule.schedule, ∀ b v, step s b v = KND_Composition.model s b v) :
 KND_Composition.execute step value KND_Schedule.schedule before =
 KND_Composition.execute KND_Composition.model value KND_Schedule.schedule before :=
 KND_Composition.schedule_composition step value before valid
#print axioms result
#print axioms conditional_writer
def applicable : List KND_Schedule.Step := [⟨"rho",304,1768,16⟩,⟨"semantic0",408,1768,16⟩,⟨"semantic1",424,1768,16⟩,⟨"semantic2",440,1768,16⟩,⟨"semantic3",456,1768,16⟩,⟨"semantic4",472,1768,16⟩,⟨"semantic5",488,1768,16⟩,⟨"semantic6",504,1768,16⟩,⟨"semantic7",520,1768,16⟩,⟨"semantic8",536,1768,16⟩,⟨"semantic9",552,1768,16⟩,⟨"z0",568,1768,16⟩,⟨"z1",584,1768,16⟩,⟨"z2",600,1768,16⟩,⟨"z3",616,1768,16⟩,⟨"power",696,1768,16⟩,⟨"weight0",712,1768,16⟩,⟨"weight1",728,1768,16⟩,⟨"weight2",744,1768,16⟩,⟨"weight3",760,1768,16⟩,⟨"weight4",776,1768,16⟩,⟨"weight5",792,1768,16⟩,⟨"weight6",808,1768,16⟩,⟨"weight7",824,1768,16⟩,⟨"weight8",840,1768,16⟩,⟨"weight9",856,1768,16⟩,⟨"weight10",872,1768,16⟩,⟨"weight11",888,1768,16⟩,⟨"weight12",904,1768,16⟩,⟨"weight13",920,1768,16⟩,⟨"weight14",936,1768,16⟩,⟨"weight15",952,1768,16⟩,⟨"weight16",968,1768,16⟩,⟨"weight17",984,1768,16⟩,⟨"weight18",1000,1768,16⟩,⟨"weight19",1016,1768,16⟩,⟨"weight20",1032,1768,16⟩,⟨"weight21",1048,1768,16⟩,⟨"weight22",1064,1768,16⟩,⟨"weight23",1080,1768,16⟩,⟨"weight24",1096,1768,16⟩,⟨"weight25",1112,1768,16⟩,⟨"weight26",1128,1768,16⟩,⟨"weight27",1144,1768,16⟩,⟨"weight28",1160,1768,16⟩,⟨"weight29",1176,1768,16⟩,⟨"weight30",1192,1768,16⟩,⟨"weight31",1208,1768,16⟩,⟨"weight32",1224,1768,16⟩,⟨"weight33",1240,1768,16⟩,⟨"weight34",1256,1768,16⟩,⟨"weight35",1272,1768,16⟩,⟨"weight36",1288,1768,16⟩,⟨"weight37",1304,1768,16⟩,⟨"weight38",1320,1768,16⟩,⟨"weight39",1336,1768,16⟩,⟨"weight40",1352,1768,16⟩,⟨"weight41",1368,1768,16⟩,⟨"weight42",1384,1768,16⟩,⟨"weight43",1400,1768,16⟩,⟨"weight44",1416,1768,16⟩,⟨"weight45",1432,1768,16⟩,⟨"weight46",1448,1768,16⟩,⟨"weight47",1464,1768,16⟩,⟨"weight48",1480,1768,16⟩,⟨"weight49",1496,1768,16⟩,⟨"weight50",1512,1768,16⟩,⟨"weight51",1528,1768,16⟩,⟨"weight52",1544,1768,16⟩,⟨"weight53",1560,1768,16⟩,⟨"weight54",1576,1768,16⟩,⟨"weight55",1592,1768,16⟩,⟨"weight56",1608,1768,16⟩,⟨"weight57",1624,1768,16⟩,⟨"weight58",1640,1768,16⟩,⟨"weight59",1656,1768,16⟩,⟨"weight60",1672,1768,16⟩,⟨"weight61",1688,1768,16⟩,⟨"weight62",1704,1768,16⟩,⟨"weight63",1720,1768,16⟩]
theorem reachable : ∀ s ∈ applicable, s ∈ KND_Schedule.schedule := by decide
theorem no_growth : ∀ s ∈ applicable, s.len+s.size≤s.cap := by decide
#print axioms reachable
#print axioms no_growth
end KND_LPi_K012
