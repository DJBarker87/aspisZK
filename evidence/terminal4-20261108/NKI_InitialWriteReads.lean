import NKI_InitialFrames
set_option autoImplicit false
namespace AspisR1.NKI_InitialWriteReads
open Aeneas Aeneas.Std Result FIq_Native
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
def Reads (l : Locals) : Prop :=
 l.q22=NJB_ArrayCarrier.cell l.initial ⟨8,by decide⟩ ∧ l.q25=NJB_ArrayCarrier.cell l.initial ⟨9,by decide⟩
theorem source (p : Public) (o : Openings) (s : Selectors) (l : Locals)
 (calls : NKI_InitialInvocation.Clauses p o s l) : Reads l := by
 have c_q22 : Array.index_usize l.initial poseidon2.RATE=ok l.q22 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_q25 : Array.index_usize l.initial1 l.i=ok l.q25 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_i : poseidon2.RATE+1#usize=ok l.i := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_initial1 : Array.update l.initial poseidon2.RATE l.q24=ok l.initial1 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have vi:=FIx_ScheduleIndices.rate_plus_one l.i c_i
 have a:=NKI_ArrayFrame.read l.initial poseidon2.RATE ⟨8,by decide⟩ l.q22 (by rw [poseidon2.RATE];rfl) c_q22
 have b:=NKI_ArrayFrame.read l.initial1 l.i ⟨9,by decide⟩ l.q25 vi c_q25
 have frame:=NKI_ArrayFrame.update l.initial l.initial1 poseidon2.RATE l.q24 c_initial1 ⟨9,by decide⟩
 simp only [poseidon2.RATE,show (8#usize).val=8 from rfl,show (⟨9,by decide⟩ : Fin (16#usize).val).val=9 from rfl,show ¬(8:Nat)=9 from by decide,if_false] at frame
 exact ⟨a,b.trans frame⟩
#print axioms source
end AspisR1.NKI_InitialWriteReads
