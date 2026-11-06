import NKK_FieldDomain
set_option autoImplicit false
noncomputable section
namespace NKU_MixedFrame
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold
/-- The successful branch's next domain is derived from the SAME replies.
Rust Err and outer abort branches are retained by the original program. -/
theorem frame (kinds : List Kind) (r last : Reader) (values : List Value)
 (bound : r.at.val+NKK_FieldDomain.span kinds≤r.bytes.val.length)
 (returned : (program kinds r).result=ok (.Ok (values,last))) :
 last.bytes=r.bytes ∧ last.at.val=r.at.val+NKK_FieldDomain.span kinds := by
 induction kinds generalizing r last values with
 | nil => cases returned;exact ⟨rfl,by simp [NKK_FieldDomain.span]⟩
 | cons kind kinds ih =>
  have firstBound : r.at.val+NKK_FieldDomain.width kind≤r.bytes.val.length := by
   simp only [NKK_FieldDomain.span,List.map_cons,List.sum_cons] at bound
   omega
  obtain ⟨reply,next,callEq,fr⟩:=NKK_FieldDomain.bounded kind r firstBound
  have nextBound : next.at.val+NKK_FieldDomain.span kinds≤next.bytes.val.length := by
   rw [fr.1]
   have advance:=fr.2
   simp only [NKK_FieldDomain.span,List.map_cons,List.sum_cons] at bound
   omega
  cases reply with
  | Err err =>
   simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,callEq] at returned
   cases returned
  | Ok value =>
   cases rest : (program kinds next).result with
   | fail err =>
    simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,callEq,rest] at returned
    cases returned
   | div =>
    simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,callEq,rest] at returned
    cases returned
   | ok inner =>
    cases inner with
    | Err err =>
     simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,callEq,rest,mapInner] at returned
     cases returned
    | Ok pair =>
     rcases pair with ⟨tail,after⟩
     have frameTail:=ih next after tail nextBound rest
     simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,callEq,rest,mapInner] at returned
     cases returned
     refine ⟨frameTail.1.trans fr.1,?_⟩
     have one:=fr.2
     have more:=frameTail.2
     simp only [NKK_FieldDomain.span,List.map_cons,List.sum_cons]
     omega
#print axioms frame
end NKU_MixedFrame
