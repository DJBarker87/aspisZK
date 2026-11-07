import PCF_DigestFirst
import PCF_LaneShape
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_CanonicalWords

theorem complete (a b c d e f g h : U32) :
    NBD_DigestInduction.Canonical (PCF_DigestFirst.words a b c d e f g h) ↔
      PCF_LaneShape.canonical a b c d e f g h := by
  constructor
  · intro canonical
    have h0 := canonical ⟨0,by decide⟩
    have h1 := canonical ⟨1,by decide⟩
    have h2 := canonical ⟨2,by decide⟩
    have h3 := canonical ⟨3,by decide⟩
    have h4 := canonical ⟨4,by decide⟩
    have h5 := canonical ⟨5,by decide⟩
    have h6 := canonical ⟨6,by decide⟩
    have h7 := canonical ⟨7,by decide⟩
    simp only [PCF_DigestFirst.words,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7
    unfold PCF_LaneShape.canonical
    scalar_tac
  · intro canonical j
    unfold PCF_LaneShape.canonical at canonical
    fin_cases j <;>
      simp only [PCF_DigestFirst.words,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] <;>
      scalar_tac

#print axioms complete
end PCF_CanonicalWords
