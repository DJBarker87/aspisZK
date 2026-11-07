import NLU_ConstructCut
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (word cell)
theorem challenges (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.challenges=f.expected.challenges := by
 have hl : (native f).value.challenges.lambda=f.expected.challenges.lambda := by
  apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 have hc : (native f).value.challenges.chi=f.expected.challenges.chi := by
  apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 have ht : (native f).value.challenges.theta=f.expected.challenges.theta := by
  apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 have hm : (native f).value.challenges.mu=f.expected.challenges.mu := by
  apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨5,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 have he : (native f).value.challenges.eta=f.expected.challenges.eta := by
  apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨6,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 have hz : (native f).value.challenges.zc=f.expected.challenges.zc := by
  apply NLU.cells_ext;intro i hi;apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
  exact (cut f).2.2.1 ⟨7,by decide⟩ ⟨0,by decide⟩ ⟨i,hi⟩ ⟨0,by decide⟩ j
 generalize (native f).value.challenges=a at hl hc ht hm he hz ⊢
 generalize f.expected.challenges=b at hl hc ht hm he hz ⊢
 cases a
 cases b
 cases hl;cases hc;cases ht;cases hz;cases hm;cases he;rfl
#print axioms challenges
end AspisR1.NLU_Construct
