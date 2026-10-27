import F3L_SemanticInventory
import F3M_OpeningChallenges
import F3M_First25Challenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_AlphaProjection
open Aeneas Aeneas.Std AspisR1PublicPreparation

theorem alpha {Hash : Type} (sem : r1_semantic.Verified Hash) (v : LiteralOpeningView.View)
    (values : v.semantic.map Prod.snd=(BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map
      (fun q=>LiteralOpeningView.eK (F3L_RhoMeaning.decode q))) :
    (fun j : Fin 10=>F3L_RhoMeaning.decode (sem.alpha.val[j.val]'(by have h : sem.alpha.val.length=10:=sem.alpha.property;omega)))=
    (fun j=>SelectedChallengeMap.rhoOf ((v.semantic.map Prod.snd).getD (15+j.val) 0)) := by
  have prefixLength : (BeginCalls.challengeList sem.challenges).length=15 := by
    simp only [BeginCalls.challengeList,List.length_cons,List.length_append,List.length_singleton,List.length_nil]
    have h : sem.challenges.zc.val.length=10 := sem.challenges.zc.property
    omega
  funext j
  rw [values,List.map_append]
  have right := List.getElem?_append_right (l₁:=(BeginCalls.challengeList sem.challenges).map
    (fun q=>LiteralOpeningView.eK (F3L_RhoMeaning.decode q)))
    (l₂:=sem.alpha.val.map (fun q=>LiteralOpeningView.eK (F3L_RhoMeaning.decode q)))
    (i:=15+j.val) (by simp only [List.length_map,prefixLength];omega)
  have index : 15+j.val-((BeginCalls.challengeList sem.challenges).map
    (fun q=>LiteralOpeningView.eK (F3L_RhoMeaning.decode q))).length=j.val := by
    simp only [List.length_map,prefixLength];omega
  simp only [List.getD,right,index,List.getElem?_map,
    List.getElem?_eq_getElem (show j.val<sem.alpha.val.length by have h : sem.alpha.val.length=10:=sem.alpha.property;omega),
    Option.map_some,Option.getD_some]
  rfl

#print axioms alpha
end AspisR1.F3M_AlphaProjection
end
