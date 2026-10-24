import S9ActualSharedHighCallsV1
import S9CanonicalPartsUpdateV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SharedHighFrameV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualSharedHighCallsV1
open AspisR1S9FactorArrayEntryV1

/-- Actual shared-high writes only slots1/3, with no arithmetic/Can premise. -/
theorem shared_high_success_frame
    (partials : Array W 4#usize) (self : weights.Weights)
    (ap0 ap1 : Array W 4#usize) (parts out : Parts)
    (h : weights.shared_high partials self ap0 ap1 parts=.ok (.Ok (),out)) :
    ∀ (j : Usize) (hj : j.val<7),j.val≠1 → j.val≠3 → atN out j hj=atN parts j hj := by
  obtain ⟨row0,row2,high0,high2,f00,f01,f20,f21,dot0,dot2,s00,s01,s20,s21,
    scale0,scale2,product0,product2,oldPart,back,hr0,hh0,hd0,hf00,hs00,hf01,hs01,
    hscale0,hproduct0,hmut,hr2,hh2,hd2,hf20,hs20,hf21,hs21,hscale2,hproduct2,hupdate⟩ :=
    shared_high_success_calls partials self ap0 ap1 parts out h
  have hb := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_mut_back_set
    parts 1#usize oldPart back (by decide) hmut
  have hu : Array.update (parts.set 1#usize product0) 3#usize product2=.ok out := by
    simpa only [hb] using hupdate
  have he := accepted_update_eq_set (parts.set 1#usize product0) 3#usize (by decide) product2 out hu
  intro j hj hn1 hn3
  have hn1' : j.val≠(1#usize).val := hn1
  have hn3' : j.val≠(3#usize).val := hn3
  rw [he,atN_set (parts.set 1#usize product0) 3#usize j product2 (by decide) hj,
    if_neg hn3',atN_set parts 1#usize j product0 (by decide) hj,if_neg hn1']

#print axioms shared_high_success_frame
end AspisR1S9SharedHighFrameV1
