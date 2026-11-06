import NKU_HeaderState
import NKU_DigestState
import NKU_WordsAt
import NKU_EAt
import NKU_KAt
set_option autoImplicit false
noncomputable section
namespace NKU_CallerScope
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKU_InputAt
/-- Explicit native cut scope; these are incoming caller facts, never inferred
from the more general source equality. CP length is derived from the header. -/
def Inputs (f : NKU.Frame) : Prop := f.proof.val.length=57607 ∧ f.publicBytes.val.length≤1880
/-- The earliest interface on ONE native parent state. Both returned facts
are the actual local bind branches in G, not positive-root hypotheses. -/
theorem header_to_roots {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s header after : NKU.State) (inputs : Inputs s.frame)
 (hh : (NKU_HeaderStep.run d s).result=ok (.Ok ((),header)))
 (hd : (NKU_DigestJoin.run d hash 1736#usize header).result=ok (.Ok ((),after))) :
 after.frame=s.frame ∧ Inputs after.frame ∧ after.decoded.endAt=some 1736#usize ∧
 At {after with reader := NKU_Roots.entry after} 80 := by
 obtain ⟨hf,hr,ho,size,ending⟩:=NKU_HeaderState.returned d s header hh
 have kept:=NKU_DigestState.preserved d hash 1736#usize header after hd
 have frame : after.frame=header.frame := congrArg Prod.fst kept
 have decoded : after.decoded=header.decoded := congrArg (fun x=>x.2.1) kept
 refine ⟨frame.trans hf,?_,?_,?_⟩
 · rw [frame,hf]
   exact inputs
 · rw [decoded]
   exact ending
 · apply NKU_HeaderState.root_entry
   rw [frame]
   exact size
/-- Concrete query windows derive352/384/408 from the same preceding reader. -/
theorem first_queries (s : NKU.State) (h : At s 320) :
 ∃ out,(NKU_FineWords.run 8 s).result=ok (.Ok ((),out)) ∧
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out 352 :=
 NKU_WordsAt.total 8 s 320 h (by decide)
theorem middle_queries (s : NKU.State) (h : At s 352) :
 ∃ out,(NKU_FineWords.run 8 s).result=ok (.Ok ((),out)) ∧
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out 384 :=
 NKU_WordsAt.total 8 s 352 h (by decide)
theorem last_queries (s : NKU.State) (h : At s 384) :
 ∃ out,(NKU_FineWords.run 6 s).result=ok (.Ok ((),out)) ∧
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out 408 :=
 NKU_WordsAt.total 6 s 384 h (by decide)
#print axioms header_to_roots
#print axioms first_queries
#print axioms middle_queries
#print axioms last_queries
end NKU_CallerScope
