import NMO_TerminalWindows
import NMC_FrameComplete
set_option autoImplicit false
namespace AspisR1.NMO_ChallengeWindows
open Aeneas Aeneas.Std AspisR1PublicPreparation
abbrev Challenges := r1_wire.Challenges
def select (c : Challenges) (k : Fin 15) : NLC_Finish.Q :=
 match h:k.val with
 | 0=>c.lambda
 | 1=>c.chi
 | 2=>c.theta
 | 3=>c.mu
 | 4=>c.eta
 | n+5=>NLU.cell c.zc n (by change n<10;have bound:=k.isLt;omega)
theorem select_zc (c : Challenges) (i : Fin 10) :
 select c ⟨i.val+5,by have h:=i.isLt;omega⟩=NLU.cell c.zc i.val i.isLt := by rfl
/-- The native k<15, limb<4 selector covers all original challenge fields,
including eta and every zc cell; field-pointer comparisons are absent. -/
theorem complete (actual expected : Challenges)
 (windows : ∀ k : Fin 15,∀ limb : Fin 4,
 NLU.word (select actual k) limb=NLU.word (select expected k) limb) : actual=expected := by
 apply NMC_Frame.challenge_ext
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨0,by decide⟩ j
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨1,by decide⟩ j
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨2,by decide⟩ j
 · apply NLU.cells_ext
   intro i hi
   change i<10 at hi
   have value:=NLU.word_ext (select actual ⟨i+5,by omega⟩) (select expected ⟨i+5,by omega⟩)
     (windows ⟨i+5,by omega⟩)
   rw [select_zc actual ⟨i,hi⟩,select_zc expected ⟨i,hi⟩] at value
   exact value
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨3,by decide⟩ j
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨4,by decide⟩ j
#print axioms select_zc
#print axioms complete
end AspisR1.NMO_ChallengeWindows
