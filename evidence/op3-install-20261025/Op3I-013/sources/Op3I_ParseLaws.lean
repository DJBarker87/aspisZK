import Op3I_Header
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace Op3I_ParseLaws
open Op3I_Source Op3I_Header

theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem source_success (proof : Slice U8) (variant : transport.Variant)
    (h : verifier.candidate.parse_shape Op3I_Std.ops proof = ok (.Ok variant)) :
    variant = .S2 ∧ proof.val.length = 57607 ∧
    proof.val.take 8 = compact.MAGIC.val ∧ proof.val[8]? = some 2#u8 ∧
    ((proof.val.drop 9).take 7).any (fun x => x != 0#u8) = false := by
  unfold verifier.candidate.parse_shape at h
  rw [proof_bytes] at h
  simp only [bind_tc_ok] at h
  split at h
  · cases h
  · rename_i hl
    have len : Slice.len proof = 57607#usize := by
      simpa only [bne_iff_ne,not_not] using hl
    have length : proof.val.length = 57607 := by
      have := congrArg UScalar.val len
      simpa using this
    obtain ⟨s,hs,h⟩ := bind_success _ _ _ h
    have sv : s.val = proof.val.take 8 := by
      simp only [core.slice.index.Slice.index,
        core.slice.index.SliceIndexRangeToUsizeSlice,
        core.slice.index.SliceIndexRangeToUsizeSlice.index] at hs
      split at hs
      · cases hs
        simp [List.slice]
      · cases hs
    simp only [core.cmp.impls.PartialEqShared.ne, Slice.Insts.CoreCmpPartialEqArray,
      Op3I_Std.ops, Op3I_Std.eqList_u8, bind_tc_ok] at h
    split at h
    · cases h
    · rename_i hm
      have magic : s.val = compact.MAGIC.val := by simpa using hm
      obtain ⟨tag,ht,h⟩ := bind_success _ _ _ h
      have tagAt : proof.val[8]? = some tag := by
        simp only [Slice.index_usize] at ht
        split at ht
        · cases ht
        · cases ht
          assumption
      simp only [transport.Variant.tag,bind_tc_ok] at h
      split at h
      · cases h
      · rename_i ht2
        have tag2 : tag = 2#u8 := by simpa only [bne_iff_ne,not_not] using ht2
        obtain ⟨tail,htail,h⟩ := bind_success _ _ _ h
        have tv : tail.val = (proof.val.drop 9).take 7 := by
          simp only [core.slice.index.Slice.index,
            core.slice.index.SliceIndexRangeUsizeSlice,
            core.slice.index.SliceIndexRangeUsizeSlice.index] at htail
          split at htail
          · cases htail
            simp [List.slice]
          · cases htail
        obtain ⟨n,hn⟩ := any_exact tail.val
        simp only [core.slice.Slice.iter,bind_tc_ok,Op3I_Std.ops,List.drop_zero,hn] at h
        split at h
        · cases h
        · rename_i hz
          have zero : tail.val.any (fun x => x != 0#u8) = false := by simpa using hz
          cases h
          exact ⟨rfl,length,sv.symm.trans magic,tagAt.trans (congrArg some tag2),tv ▸ zero⟩

#print axioms bind_success
#print axioms source_success
end Op3I_ParseLaws
end
