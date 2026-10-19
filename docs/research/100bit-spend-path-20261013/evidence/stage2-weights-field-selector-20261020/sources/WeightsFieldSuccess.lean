import WeightsFieldExplicitDecoder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1WeightsFieldCurrent.WeightsFieldSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem checked_slice_decode {T : Type} (decode : Slice U8 → Result (Option T))
    (bytes : Slice U8) (i : Usize) (value : T)
    (h : weights.field decode bytes i = .ok value) :
    ∃ start next finish selected,
      (i * 32#usize : Result Usize) = .ok start ∧
      (i + 1#usize : Result Usize) = .ok next ∧
      (next * 32#usize : Result Usize) = .ok finish ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes { start := start, «end» := finish } = .ok selected ∧
      decode selected = .ok (some value) := by
  unfold weights.field at h
  obtain ⟨start,hs,h⟩ := bind_success _ _ _ h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  obtain ⟨finish,hf,h⟩ := bind_success _ _ _ h
  obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
  obtain ⟨o,hdecode,h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp [core.option.Option.unwrap] at h
  | some decoded =>
    have heq : decoded = value := by simpa [core.option.Option.unwrap] using h
    subst decoded
    exact ⟨start,next,finish,selected,hs,hn,hf,hselected,hdecode⟩

theorem canonical {T : Type} (decode : Slice U8 → Result (Option T))
    (Canonical : T → Prop)
    (decoderLaw : ∀ bytes value, decode bytes = .ok (some value) → Canonical value)
    (bytes : Slice U8) (i : Usize) (value : T)
    (h : weights.field decode bytes i = .ok value) : Canonical value := by
  obtain ⟨_,_,_,selected,_,_,_,_,hdecoded⟩ := checked_slice_decode decode bytes i value h
  exact decoderLaw selected value hdecoded
#print axioms checked_slice_decode
#print axioms canonical
end AspisR1WeightsFieldCurrent.WeightsFieldSuccess
