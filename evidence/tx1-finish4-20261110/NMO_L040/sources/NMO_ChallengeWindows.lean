import NMO_TerminalWindows
import NMC_FrameComplete
set_option autoImplicit false
namespace AspisR1.NMO_ChallengeWindows
open Aeneas Aeneas.Std AspisR1PublicPreparation
abbrev Challenges := r1_wire.Challenges
def select (c : Challenges) (k : Fin 15) : NLC_Finish.Q :=
 if h0:k.val=0 then c.lambda
 else if h1:k.val=1 then c.chi
 else if h2:k.val=2 then c.theta
 else if h3:k.val=3 then c.mu
 else if h4:k.val=4 then c.eta
 else NLU.cell c.zc (k.val-5) (by change k.val-5<10;have bound:=k.isLt;omega)
theorem select_zc (c : Challenges) (i : Fin 10) :
 select c ⟨i.val+5,by have h:=i.isLt;omega⟩=NLU.cell c.zc i.val i.isLt := by
 simp only [select,show i.val+5≠0 by omega,dif_neg,
  show i.val+5≠1 by omega,show i.val+5≠2 by omega,
  show i.val+5≠3 by omega,show i.val+5≠4 by omega,ite_false,Nat.add_sub_cancel]
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
   have value:=NLU.word_ext (select actual ⟨i+5,by omega⟩) (select expected ⟨i+5,by omega⟩)
     (windows ⟨i+5,by omega⟩)
   rw [select_zc actual ⟨i,hi⟩,select_zc expected ⟨i,hi⟩] at value
   exact value
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨3,by decide⟩ j
 · apply NLU.word_ext;intro j;simpa [select] using windows ⟨4,by decide⟩ j
#print axioms select_zc
#print axioms complete
end AspisR1.NMO_ChallengeWindows
