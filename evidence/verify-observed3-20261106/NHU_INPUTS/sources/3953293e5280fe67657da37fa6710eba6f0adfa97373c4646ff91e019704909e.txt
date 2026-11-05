import NHU_TransitionStep
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result WP
namespace AspisR1.NHU_TransitionExpected
open FIq_Native.pool_v1.pair_forest_semantic_terminal
open NHU_TransitionCut

theorem empty (level : Usize) (inside : level.val<20) :
 ∃ root,empty_root level=ok root := by
 have call:=ExtractedMaskHornerStep.array_index_usize_ok constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level (by change level.val<21;omega)
 rw [NHG_ExtraLeaves.empty_source]
 exact ⟨_,call⟩

theorem shift (index : U64) (level : Usize) (inside : level.val<20) :
 ∃ out,(index >>> level : Result U64)=ok out := by
 have spec : (index >>> level : Result U64) ⦃ _=>True ⦄ := by
  step* <;> scalar_tac
 obtain ⟨out,call,_⟩:=WP.spec_imp_exists spec
 exact ⟨out,call⟩

theorem result (p : Public) (level carry : Usize) (inside : level.val<20) :
 ∃ want,NHU_TransitionStep.expected p level carry=ok want := by
 unfold NHU_TransitionStep.expected
 by_cases earlier : level<carry
 · rw [if_pos earlier]
   exact empty level inside
 · rw [if_neg earlier]
   obtain ⟨out,call⟩:=shift p.transition.live_snapshot.next_pair_index level inside
   rw [call,bind_tc_ok]
   simp only [lift,bind_tc_ok]
   split
   · exact empty level inside
   · exact ⟨_,ExtractedMaskHornerStep.array_index_usize_ok p.transition.live_snapshot.frontier level inside⟩
#print axioms empty
#print axioms shift
#print axioms result
end AspisR1.NHU_TransitionExpected
end
