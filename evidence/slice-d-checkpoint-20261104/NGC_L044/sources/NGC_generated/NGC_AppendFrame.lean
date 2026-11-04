import NGC_KNE_Final
import KMX_CopyMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_AppendFrame
open AspisV8R19.DuplexFrames
/-- Exact byte-loop value law of the prescribed KMX implementation. -/
theorem bytes (before value : Bytes) : KMX_CopyMeaning.appendLoop before value=before++value :=
 KMX_CopyMeaning.append_spec before value
/-- Prefix observations survive every composed byte window. -/
theorem prefix (before value : Bytes) (j : Nat) (inside : j<before.length) :
 (KMX_CopyMeaning.appendLoop before value)[j]?=before[j]? := by
 rw [bytes,List.getElem?_append_left inside]
/-- The one-byte native precondition holds at EVERY byte of EVERY transition,
including checksum and the last weight. No larger-buffer replay is needed. -/
theorem byte_domain (s : NGC_KND_Schedule.Step) (member : s∈NGC_KND_Schedule.schedule)
 (i : Nat) (inside : i<s.size) : s.len+i<1768 ∧ i<32 := by
 have bounds := NGC_KND_Schedule.no_growth s member
 have caps : ∀ s∈NGC_KND_Schedule.schedule,s.cap=1768 := by decide
 have sizes : ∀ s∈NGC_KND_Schedule.schedule,s.size≤32 := by decide
 have cap := caps s member
 have size := sizes s member
 omega
/-- Value relation interpreted by the controlled byte-step packet. Physical
allocation, unique borrow and source association retain their explicit P6 row. -/
def Native (before value after : Bytes) : Prop := after=KMX_CopyMeaning.appendLoop before value
/-- Discharges KNE's abstract local-correctness input by the permanent KMX
value law, rather than treating it as an independent successful-write input. -/
theorem local_correct : NGC_KNE_Composition.LocalCorrect Native NGC_KND_Schedule.schedule := by
 intro step member before value after beforeLength valueLength native
 exact native.trans (bytes before value)
#print axioms bytes
#print axioms prefix
#print axioms byte_domain
#print axioms local_correct
end AspisR1.NGC_AppendFrame
end
