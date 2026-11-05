import NGY_Decoder
import NGU_Part007
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_DirectRead
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- The handwritten four-word reference reads the SAME physical928-byte y1,
not an independently selected32-byte surrogate. All decoder replies and
canonicality are derived from the local byte domain. -/
theorem source {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
 (length : y1.val.length=928) (domain : NGU_LPq_SelectedDomain.ByteDomain y1)
 (lane point : Usize) (hl : lane.val<29) (hp : point.val=5) :
 ∃ b, NGU_LPq_SelectedDomain.selected y1 lane=ok b ∧ b.val.length=32 ∧
  b.val=(y1.val.drop (32*lane.val)).take 32 ∧
  canonQ (NGY_Decoder.scalar b) ∧
  ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=ok (qPort (NGY_Decoder.scalar b)) ∧
  (∀ j : Nat, j<4 → (NGU_LPq_BytesTotal.word b j).val=
   NGU_LPr_SelectedWords.naturalWord y1.val (32*lane.val+4*j)) := by
 obtain ⟨b,window,len,canonical,read⟩ := NGY_Decoder.selected sem y1 domain lane hl point hp
 obtain ⟨actual,slice,size,same⟩ := NGU_LPr_SelectedBytes.selected y1 length lane hl
 change NGU_LPq_SelectedDomain.selected y1 lane=ok actual at slice
 have eq : actual=b := Result.ok.inj (slice.symm.trans window)
 subst actual
 refine ⟨b,window,len,same,canonical,read,?_⟩
 intro j hj
 exact NGU_LPr_SelectedWords.window_word y1.val b (32*lane.val) j same (by omega)

#print axioms source
end AspisR1.NGY_DirectRead
end
