import NHU_TransitionGuardValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_TransitionWords
open FIq_Native.pool_v1.pair_forest_semantic_terminal
open NHU_TransitionCut
def cell (a : Array U32 8#usize) (i : Fin 8) : U32 :=
 a.val[i.val]'(by scalar_tac)

def same8 (a b : Array U32 8#usize) : Prop :=
 cell a ⟨0,by decide⟩=cell b ⟨0,by decide⟩ ∧
 cell a ⟨1,by decide⟩=cell b ⟨1,by decide⟩ ∧
 cell a ⟨2,by decide⟩=cell b ⟨2,by decide⟩ ∧
 cell a ⟨3,by decide⟩=cell b ⟨3,by decide⟩ ∧
 cell a ⟨4,by decide⟩=cell b ⟨4,by decide⟩ ∧
 cell a ⟨5,by decide⟩=cell b ⟨5,by decide⟩ ∧
 cell a ⟨6,by decide⟩=cell b ⟨6,by decide⟩ ∧
 cell a ⟨7,by decide⟩=cell b ⟨7,by decide⟩

theorem same_iff (a b : Array U32 8#usize) : same8 a b ↔ a=b := by
 constructor
 · intro h
   rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
   have point : ∀ i : Fin 8,cell a i=cell b i := by
    intro ⟨i,hi⟩
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases cases with h|h|h|h|h|h|h|h
    · subst i;simpa only [cell] using h0
    · subst i;simpa only [cell] using h1
    · subst i;simpa only [cell] using h2
    · subst i;simpa only [cell] using h3
    · subst i;simpa only [cell] using h4
    · subst i;simpa only [cell] using h5
    · subst i;simpa only [cell] using h6
    · subst i;simpa only [cell] using h7
   apply Subtype.ext
   apply List.ext_getElem
   · have ha:=a.property;have hb:=b.property;omega
   · intro i ha hb
     exact point ⟨i,by scalar_tac⟩
 · intro same;subst b;unfold same8;exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem different (a b : Array U32 8#usize) : ¬same8 a b ↔ a≠b :=
 not_congr (same_iff a b)

theorem guard (p : Public) (level carry : Usize) (inside : level.val<20) :
 ∃ want got,NHU_TransitionStep.expected p level carry=ok want ∧
 Array.index_usize p.transition.candidate_afterstate.next_frontier level=ok got ∧
 NHU_TransitionGuard.guard p level carry=
 ok (if level=carry ∧ carry<20#usize then .Ok ()
 else if ¬same8 got want then .Err .InvalidAppendTransition else .Ok ()) := by
 obtain ⟨want,got,expected,get,run⟩:=NHU_TransitionGuardValue.result p level carry inside
 refine ⟨want,got,expected,get,?_⟩
 rw [run]
 by_cases skip : level=carry ∧ carry<20#usize
 · simp only [if_pos skip]
 · simp only [if_neg skip]
   by_cases equal : got=want
   · have h:= (same_iff got want).mpr equal
     simp only [if_pos equal,not_not,if_neg (not_not_intro h)]
   · have h : ¬same8 got want := (different got want).mpr equal
     simp only [if_neg equal,if_pos h]

#print axioms same_iff
#print axioms different
#print axioms guard
end AspisR1.NIH_TransitionWords
end
