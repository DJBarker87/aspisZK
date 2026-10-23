import S9NativeArrayCanonicalV1
import S9NativeWideDecodedArithmeticV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9S2WeightCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeArrayCanonicalV1
abbrev R := core.ops.range.Range Usize
abbrev Low := Array W 16#usize
private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Exact source continuation either keeps its weight or adds its actual
successfully read low entry. Static masks are never unfolded. -/
theorem weight_body_cont_source (low : Low) (group : Usize) (iter iterOut : R) (weight out : W)
    (h : weights.s2_grouped_inactive_pair_loop1_loop0.body low group iter weight=
      .ok (.cont (iterOut,out))) :
    ∃ bit, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some bit,iterOut) ∧
      (out=weight ∨ ∃ challenge,
        Array.index_usize low bit=.ok challenge ∧
        aspis_core.field.wide_exact.WideExact.add weight challenge=.ok out) := by
  unfold weights.s2_grouped_inactive_pair_loop1_loop0.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some bit =>
    obtain ⟨challenge,hread,h⟩ := bind_success _ _ _ h
    obtain ⟨mask,hmask,h⟩ := bind_success _ _ _ h
    obtain ⟨shift,hshift,h⟩ := bind_success _ _ _ h
    obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
    split at h
    · obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨bit,hn,Or.inr ⟨challenge,hread,hadd⟩⟩
    · have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨bit,hn,Or.inl rfl⟩

theorem weight_body_done_same (low : Low) (group : Usize) (iter : R) (weight out : W)
    (h : weights.s2_grouped_inactive_pair_loop1_loop0.body low group iter weight=.ok (.done out)) :
    out=weight := by
  unfold weights.s2_grouped_inactive_pair_loop1_loop0.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact (ControlFlow.done.inj (Result.ok.inj h)).symm
  | some bit =>
    obtain ⟨challenge,hread,h⟩ := bind_success _ _ _ h
    obtain ⟨mask,hmask,h⟩ := bind_success _ _ _ h
    obtain ⟨shift,hshift,h⟩ := bind_success _ _ _ h
    obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
    split at h
    · obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
      cases h
    · cases h

/-- Actual accepted masked-low accumulation is canonical from its actual
low entries and initial carry. No source mask values or child successes are
assumed, and no raw-dot implementation is used. -/
theorem weight_loop_success_canonical (low : Low) (group : Usize) (iter : R) (weight out : W)
    (hlow : ReadsCanonical low) (hweight : Canonical weight)
    (hloop : weights.s2_grouped_inactive_pair_loop1_loop0 iter low group weight=.ok out) : Canonical out := by
  let step := fun s : R × W => weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2
  let inv := fun s : R × W => Canonical s.2
  let measure := fun s : R × W => s.1.end.val-s.1.start.val
  have hd : ∀ s result, inv s → step s=.ok (.done result) → Canonical result := by
    rintro ⟨r,c⟩ result hc hb
    have he := weight_body_done_same low group r c result hb
    exact he.symm ▸ hc
  have hc : ∀ s s', inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hc hb
    obtain ⟨bit,hn,he⟩ := weight_body_cont_source low group r r' c c' hb
    cases he with
    | inl he => exact he.symm ▸ hc
    | inr he =>
      obtain ⟨challenge,hread,hadd⟩ := he
      exact (AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded
        c challenge c' hc (hlow bit challenge hread) hadd).1
  have hm : ∀ s s', step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hb
    obtain ⟨bit,hn,he⟩ := weight_body_cont_source low group r r' c c' hb
    obtain ⟨hlt,hbit,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' bit hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv (iter,weight) := hweight
  have hl : Aeneas.Std.loop step (iter,weight)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv Canonical hd hc hm _ out hinit hl

#print axioms weight_body_cont_source
#print axioms weight_body_done_same
#print axioms weight_loop_success_canonical
end AspisR1S9S2WeightCanonicalV1
