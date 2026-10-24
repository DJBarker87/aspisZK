import S9S3MaskBitReadOnlyV1
import S9S2WeightCanonicalV1
import S9ActualDotRangeBoundsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9NativeS3WeightBodyV1
open AspisR1S9ProductionPairCutV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev R := core.ops.range.Range Usize
abbrev Low := Array W 16#usize
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev decode := AspisR1S9NativeWideDecodedArithmeticV1.decode
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m;next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- SAME native Range16 continuation supplies its real low and mask reads and
exact integer-bit-selected decoded increment. No desired mask/shift/add event
or semantic contribution is supplied as a premise. -/
theorem native_weight_cont_decoded (low : Low) (group : Usize) (iter iterOut : R)
    (weight out : W) (hend : iter.end.val ≤ 16)
    (hlow : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical low) (hweight : Can weight)
    (hbody : weights.s2_grouped_inactive_pair_loop1_loop0.body low group iter weight=
      .ok (.cont (iterOut,out))) :
    ∃ (bit : Usize) (challenge : W) (mask : U16),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some bit,iterOut) ∧
      Array.index_usize low bit=.ok challenge ∧
      Array.index_usize weights.S2_INACTIVE_MASKS group=.ok mask ∧ bit.val<16 ∧
      Can out ∧ decode out=decode weight+
        (if (mask.val /2^bit.val)%2=1 then decode challenge else 0) := by
  unfold weights.s2_grouped_inactive_pair_loop1_loop0.body at hbody
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ hbody
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some bit =>
    obtain ⟨challenge,hread,h⟩ := bind_success _ _ _ h
    obtain ⟨mask,hmask,h⟩ := bind_success _ _ _ h
    obtain ⟨power,hpower,h⟩ := bind_success _ _ _ h
    obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
    have hp : power=AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit := (Result.ok.inj hpower).symm
    subst power
    have hs : selected=(mask &&& AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit) :=
      (Result.ok.inj hselected).symm
    subst selected
    have hj := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter iterNext bit hn).2.1
    have hb : bit.val<16 := by omega
    have htest := AspisR1S9S3MaskBitReadOnlyV1.native_mask_test_matches_bit mask bit hb
    by_cases hselect : ((mask &&& AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit) != 0#u16)=true
    · simp only [if_pos hselect] at h
      obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
      have he : (iterNext,total)=(iterOut,out) := ControlFlow.cont.inj (Result.ok.inj h)
      have hi := congrArg Prod.fst he
      change iterNext=iterOut at hi
      have ho := congrArg Prod.snd he
      change total=out at ho
      subst iterNext;subst total
      obtain ⟨hout,heq⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded
        weight challenge out hweight (hlow bit challenge hread) hadd
      have hbit : (mask.val /2^bit.val)%2=1 := htest.mp hselect
      exact ⟨bit,challenge,mask,hn,hread,hmask,hb,hout,by simpa only [if_pos hbit] using heq⟩
    · simp only [if_neg hselect] at h
      have he : (iterNext,weight)=(iterOut,out) := ControlFlow.cont.inj (Result.ok.inj h)
      have hi := congrArg Prod.fst he
      change iterNext=iterOut at hi
      have ho := congrArg Prod.snd he
      change weight=out at ho
      subst iterNext;subst out
      have hbit : ¬ (mask.val /2^bit.val)%2=1 := fun hm => hselect (htest.mpr hm)
      exact ⟨bit,challenge,mask,hn,hread,hmask,hb,hweight,by simp only [if_neg hbit,add_zero]⟩

#print axioms native_weight_cont_decoded
end AspisR1S9NativeS3WeightBodyV1
