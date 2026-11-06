import NKI_InitialInvocation
import NKI_ArrayFrame
set_option autoImplicit false
namespace AspisR1.NKI_InitialReads
open Aeneas Aeneas.Std Result
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
def Reads (s : Selectors) (l : Locals) : Prop :=
 l.q=NJB_ArrayCarrier.cell s.high ⟨0,by decide⟩ ∧
 l.q1=NJB_ArrayCarrier.cell s.high ⟨1,by decide⟩ ∧
 l.q3=NJB_ArrayCarrier.cell s.high ⟨25,by decide⟩ ∧
 l.q5=NJB_ArrayCarrier.cell s.high ⟨30,by decide⟩ ∧
 l.q6=NJB_ArrayCarrier.cell s.high ⟨27,by decide⟩ ∧
 l.q7=NJB_ArrayCarrier.cell s.high ⟨28,by decide⟩ ∧
 l.q8=NJB_ArrayCarrier.cell s.high ⟨29,by decide⟩ ∧
 l.q9=NJB_ArrayCarrier.cell s.low ⟨0,by decide⟩ ∧
 l.q29=NJB_ArrayCarrier.cell s.high ⟨2,by decide⟩ ∧
 l.q32=NJB_ArrayCarrier.cell s.high ⟨26,by decide⟩ ∧
 l.q35=NJB_ArrayCarrier.cell s.high ⟨31,by decide⟩ ∧
 l.q36=NJB_ArrayCarrier.cell s.high ⟨3,by decide⟩ ∧
 l.q37=NJB_ArrayCarrier.cell s.high ⟨32,by decide⟩ ∧
 l.q38=NJB_ArrayCarrier.cell s.low ⟨12,by decide⟩
theorem source (p : Public) (o : Openings) (s : Selectors) (l : Locals)
 (calls : NKI_InitialInvocation.Clauses p o s l) : Reads s l := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact NKI_ArrayFrame.read s.high 0#usize _ l.q rfl (calls.2.2.1)
 · exact NKI_ArrayFrame.read s.high 1#usize _ l.q1 rfl (calls.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 25#usize _ l.q3 rfl (calls.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 30#usize _ l.q5 rfl (calls.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 27#usize _ l.q6 rfl (calls.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 28#usize _ l.q7 rfl (calls.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 29#usize _ l.q8 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.low 0#usize _ l.q9 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 2#usize _ l.q29 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 26#usize _ l.q32 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 31#usize _ l.q35 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 3#usize _ l.q36 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.high 32#usize _ l.q37 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
 · exact NKI_ArrayFrame.read s.low 12#usize _ l.q38 rfl (calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
#print axioms source
end AspisR1.NKI_InitialReads
