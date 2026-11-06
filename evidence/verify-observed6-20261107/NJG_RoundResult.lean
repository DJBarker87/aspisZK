import NIX_CertificateFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_RoundResult
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
attribute [local instance] Classical.propDecidable

/-- Complete alpha carrier assembled from the original native windows. -/
def alpha (s : RoundPre) : Alpha :=
 ⟨List.ofFn (alphaCell s),by simp⟩

theorem alpha_cell (s : RoundPre) (j : Fin 10) :
 cell (alpha s) j=alphaCell s j := by
 simp only [alpha,cell,FJb_TailCell.cell,List.getElem_ofFn]

/-- All windows belong to the SAME post. No separately chosen output or
success assumption is introduced. Child replies here are opaque cut inputs;
substitution by CLOSED child clauses is still required at the root. -/
def reply (s : RoundPre) : RoundOutput :=
 match s.polynomial with
 | .Err error=>.Err error
 | .Ok _=>if s.boundary≠s.running then .Err (.Boundary s.round) else
   match s.semantic with
   | .Err error=>.Err error
   | .Ok _=>.Ok (s.value,alpha s,s.newState,s.newNext)

theorem complete (s : RoundPre) (post : RoundOutput)
 (windows : ∀ j z,roundResult s j z post) : post=reply s := by
 have first:= (windows 0 0).2
 cases hp:s.polynomial with
 | Err error=>simpa only [reply,hp,roundResult] using first
 | Ok polynomial=>
   by_cases hb:s.boundary≠s.running
   · simpa only [reply,hp,if_pos hb] using first
   · cases hs:s.semantic with
     | Err error=>simpa only [reply,hp,hb,if_false,hs] using first
     | Ok challenge=>
       simp only [hp,hb,if_false,hs] at first
       obtain ⟨a,state,rfl,_,_⟩:=first
       have each : ∀ j z,cell a j=alphaCell s j ∧ cell state z=cell s.newState z := by
        intro j z
        have w:=(windows j z).2
        simp only [hp,hb,if_false,hs] at w
        obtain ⟨a',state',eq,ha,hstate⟩:=w
        have same:=core.result.Result.Ok.inj eq
        have ea : a=a':=congrArg (fun v=>v.2.1) same
        have es : state=state':=congrArg (fun v=>v.2.2.1) same
        exact ⟨ea.symm ▸ ha,es.symm ▸ hstate⟩
       have aa : a=alpha s := array_ext a (alpha s) (fun j=>(each j ⟨0,by decide⟩).1.trans (alpha_cell s j).symm)
       have st : state=s.newState := array_ext state s.newState (fun z=>(each ⟨0,by decide⟩ z).2)
       simp only [reply,hp,hb,if_false,hs,aa,st]

#print axioms alpha_cell
#print axioms complete
end AspisR1.NJG_RoundResult
end
