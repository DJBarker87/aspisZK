import RPu_RawPoseidonExtensionSlice
import ExtractedMaskReducer
import ExtractedMaskTowerAdd
import RPu_RawPoseidonExternalRowReads

/-! The exact candidate's extension conversion, reusing the checked current
U64 reducer. This does not construct raw limbs or model `array::from_fn`. -/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExtensionWords

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open ExtractedMaskTowerAdd
open RawPoseidonExternalRowReads

abbrev Limbs := Array U64 4#usize

def limbAt (xs : Limbs) (j : Fin 4) : U64 :=
  xs.val[j.val]'(by simpa [xs.property] using j.isLt)

/-- The release extraction of `reduce_u62` delegates to the total U64
reducer. The source's debug assertion is absent in this pinned extraction. -/
theorem current_reduce_u62_mod (x : U64) :
    ∃ z : field.M31, field.M31.reduce_u62 x = .ok z ∧
      z.val = x.val % P ∧ z.val < P := by
  obtain ⟨z, hz, hm, hc⟩ := ExtractedMaskReducer.current_reduce_mod x
  exact ⟨z, by simp only [field.M31.reduce_u62, hz, bind_tc_ok], hm, hc⟩

theorem extension_from_raw_limbs_words (xs : Limbs) :
    ∃ q : field.QM31,
      state_only_poseidon.extension_from_raw_limbs xs = .ok q ∧
      CanonicalQM q ∧
      wordsQM q =
        (((limbAt xs 0).val % P, (limbAt xs 1).val % P),
         ((limbAt xs 2).val % P, (limbAt xs 3).val % P)) := by
  have h0 : Array.index_usize xs 0#usize = .ok (limbAt xs 0) := by
    simpa [limbAt] using array_index_usize_ok xs 0#usize (by decide)
  have h1 : Array.index_usize xs 1#usize = .ok (limbAt xs 1) := by
    simpa [limbAt] using array_index_usize_ok xs 1#usize (by decide)
  have h2 : Array.index_usize xs 2#usize = .ok (limbAt xs 2) := by
    simpa [limbAt] using array_index_usize_ok xs 2#usize (by decide)
  have h3 : Array.index_usize xs 3#usize = .ok (limbAt xs 3) := by
    simpa [limbAt] using array_index_usize_ok xs 3#usize (by decide)
  obtain ⟨a, ha, va, ca⟩ := current_reduce_u62_mod (limbAt xs 0)
  obtain ⟨b, hb, vb, cb⟩ := current_reduce_u62_mod (limbAt xs 1)
  obtain ⟨c, hc, vc, cc⟩ := current_reduce_u62_mod (limbAt xs 2)
  obtain ⟨d, hd, vd, cd⟩ := current_reduce_u62_mod (limbAt xs 3)
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, ?_, ⟨⟨ca,cb⟩,⟨cc,cd⟩⟩, ?_⟩
  · simp only [state_only_poseidon.extension_from_raw_limbs, h0, h1, h2, h3,
      ha, hb, hc, hd, field.CM31.new, bind_tc_ok]
  · exact Prod.ext (Prod.ext va vb) (Prod.ext vc vd)

theorem extension_limbs_words (q : field.QM31) :
    state_only_poseidon.extension_limbs q =
      .ok (Array.make 4#usize [q.c0.a, q.c0.b, q.c1.a, q.c1.b]) := by
  rfl

#print axioms current_reduce_u62_mod
#print axioms extension_from_raw_limbs_words
#print axioms extension_limbs_words
end AspisR1.RawPoseidonExtensionWords
