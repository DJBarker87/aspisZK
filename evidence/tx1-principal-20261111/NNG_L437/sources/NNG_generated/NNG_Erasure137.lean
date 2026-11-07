import NNG_Tree137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Erasure137
open Aeneas Aeneas.Std Result NMP_prepare NNG_Context137 NMT_CallTree

theorem source {H : Type} (c : Calls) (s : Parent H) : erase (NNG_Tree137.tree c s)=emitted c s := by
  unfold NNG_Tree137.tree NNG_Context137.emitted NMP_prepare.r1_semantic.verify_observed
  rw [erase_bind,erase_invoke]
  apply NMT_CallTree.result_congr
  intro reply
  cases reply with
  | Err e=>rfl
  | Ok p=>
    unfold NNG_Tree137.mark0
    rw [erase_bind,erase_invoke]
    apply NMT_CallTree.result_congr
    intro u
    unfold NNG_Tree137.publicTranscript
    rw [erase_bind,erase_invoke]
    apply NMT_CallTree.result_congr
    intro reply
    cases reply with
    | Err e=>rfl
    | Ok t=>
      unfold NNG_Tree137.begin_
      rw [erase_bind,erase_invoke]
      apply NMT_CallTree.result_congr
      intro pair
      rcases pair with ⟨reply,after⟩
      cases reply with
      | Err e=>rfl
      | Ok ch=>
        unfold NNG_Tree137.mark1
        rw [erase_bind,erase_invoke]
        apply NMT_CallTree.result_congr
        intro u
        exact erase_invoke _ _ _
#print axioms source
end AspisR1.NNG_Erasure137
