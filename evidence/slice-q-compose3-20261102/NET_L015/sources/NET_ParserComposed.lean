import NEO_QModelBinding
import NEB_PureFrame
set_option autoImplicit false
namespace NET_ParserComposed
open Aeneas Aeneas.Std Result AspisR1
open S8OwnedP6FieldParserTransport

def recoverC (w : Array U32 2#usize) : ActualC :=
 ⟨w.val[0]?.getD 0#u32,w.val[1]?.getD 0#u32⟩
def recoverQ (w : Array U32 4#usize) : ActualQ :=
 ⟨⟨w.val[0]?.getD 0#u32,w.val[1]?.getD 0#u32⟩,
  ⟨w.val[2]?.getD 0#u32,w.val[3]?.getD 0#u32⟩⟩

theorem c_roundtrip (x : ActualC) :
 recoverC (NEO_ComplexReference.observe (cToCandidate x))=x := by cases x; rfl

theorem q_roundtrip (x : ActualQ) :
 recoverQ (NEO_QuadraticCuts.observe (qToCandidate x))=x := by
 rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
 rfl

def complex (bytes : Slice U8) : Result (Option ActualC) :=
 mapResult (Option.map recoverC) (NEO_WindowV2.complex bytes)
def quadratic (bytes : Slice U8) : Result (Option ActualQ) :=
 mapResult (Option.map recoverQ) (NEO_WindowV2.quadratic bytes)

/-- Complete same-input nominal Result, including None, failure and divergence.
The native counterpart checks the SAME borrowed full-allocation windows. -/
theorem complex_result (bytes : Slice U8) (bound : 8≤bytes.val.length) :
 complex bytes=S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes := by
 unfold complex
 rw [NEO_QModelBinding.complex bytes bound]
 cases h:S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes with
 | ok o => cases o <;> simp only [mapResult,Option.map,c_roundtrip]
 | fail e => rfl
 | div => rfl

theorem quadratic_result (bytes : Slice U8) (bound : 16≤bytes.val.length) :
 quadratic bytes=S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes := by
 unfold quadratic
 rw [NEO_QModelBinding.quadratic bytes bound]
 cases h:S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes with
 | ok o => cases o <;> simp only [mapResult,Option.map,q_roundtrip]
 | fail e => rfl
 | div => rfl

theorem complex_result_state_effects {S Event : Type} (state : S)
 (bytes : Slice U8) (bound : 8≤bytes.val.length) :
 NEB_PureFrame.run (Event:=Event) state (complex bytes)=
 NEB_PureFrame.run state (S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes) := by
 rw [complex_result bytes bound]

theorem quadratic_result_state_effects {S Event : Type} (state : S)
 (bytes : Slice U8) (bound : 16≤bytes.val.length) :
 NEB_PureFrame.run (Event:=Event) state (quadratic bytes)=
 NEB_PureFrame.run state (S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes) := by
 rw [quadratic_result bytes bound]

#print axioms c_roundtrip
#print axioms q_roundtrip
#print axioms complex_result
#print axioms quadratic_result
#print axioms complex_result_state_effects
#print axioms quadratic_result_state_effects
end NET_ParserComposed
