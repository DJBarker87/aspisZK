import DigestFixedBinding
import ExtractedMaskConstants

set_option autoImplicit false
namespace AspisR1.DigestFixedPrefix
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
open AspisR1.DigestFixedBinding
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev DigestWordsCanonical (d : Array M31 8#usize) : Prop :=
  ∀ j : Fin 8, (d.val[j.val]'(by simpa [d.property] using j.isLt)).val <
    AspisR1.ExtractedMaskTowerAdd.P

def zero : Array QM 8#usize := Array.repeat 8#usize field.QM31.ZERO

theorem zero_canonical : CanonicalArray zero := by
  intro j
  change AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
    ((List.replicate 8 field.QM31.ZERO)[j.val]'(by simpa using j.isLt))
  rw [List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_canonical

theorem zero_decoded : decoded zero = (fun _ => 0) := by
  funext j
  change AspisR1.ExtractedMaskQM31Exact.decode (cellAt zero j.val) = 0
  unfold cellAt
  rw [dif_pos j.isLt]
  change AspisR1.ExtractedMaskQM31Exact.decode
    ((List.replicate 8 field.QM31.ZERO)[j.val]'(by simpa using j.isLt)) = 0
  rw [List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_decode

/-- The first four bindings of the actual wrapper, factored only at the
repeated checked-row/binding fragment. The recipient presence branch is kept. -/
def fixedPrefix (public1 : Public) (opened : Array QM 16#usize)
    (selectors : Selectors) : Result (Array QM 8#usize) := do
  let d1 ← bindBlock zero opened selectors 56#usize public1.anchor
  let d2 ← bindBlock d1 opened selectors 26#usize public1.nullifier
  let d3 ← match public1.recipient with
    | none => .ok d2
    | some recipient => bindBlock d2 opened selectors 29#usize recipient
  bindBlock d3 opened selectors 32#usize public1.change

@[irreducible] def step (point : Array QM 10#usize) (opened : Array QM 16#usize)
    (block : Fin 64) (target : Array M31 8#usize) (acc : R0P.Digest ExactQM) :
    R0P.Digest ExactQM :=
  R0P.digestAddBinding acc (pointSelector point ⟨block.val * 16 + 11, by omega⟩)
    (openedModel opened) 0 (SemanticPublicModel.digest target)

@[irreducible] def model (point : Array QM 10#usize) (opened : Array QM 16#usize)
    (public1 : Public) : R0P.Digest ExactQM :=
  let d1 := step point opened 56 public1.anchor (fun _ => 0)
  let d2 := step point opened 26 public1.nullifier d1
  let d3 := match public1.recipient with
    | none => d2
    | some recipient => step point opened 29 recipient d2
  step point opened 32 public1.change d3

attribute [local irreducible] R0P.digestAddBinding
  AspisR1.SelectorValueLaneModelComposition.pointSelector

theorem source_success (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (opened : Array QM 16#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray opened)
    (ha : DigestWordsCanonical public1.anchor)
    (hn : DigestWordsCanonical public1.nullifier)
    (hc : DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → DigestWordsCanonical recipient) :
    ∃ out, fixedPrefix public1 opened selectors = .ok out ∧ CanonicalArray out ∧
      decoded out = model point opened public1 := by
  obtain ⟨d1, h1, hc1, hv1⟩ := bindBlock_success point selectors zero opened 56#usize
    public1.anchor (by decide) hpoint hbox zero_canonical hopened ha
  have h1m : decoded d1 = step point opened 56 public1.anchor (fun _ => 0) := by
    unfold step
    funext j
    rw [hv1 j, zero_decoded]
    rfl
  obtain ⟨d2, h2, hc2, hv2⟩ := bindBlock_success point selectors d1 opened 26#usize
    public1.nullifier (by decide) hpoint hbox hc1 hopened hn
  have h2m : decoded d2 = step point opened 26 public1.nullifier (decoded d1) := by
    unfold step
    exact funext hv2
  rw [h1m] at h2m
  cases hrec : public1.recipient with
  | none =>
    obtain ⟨out, ho, hco, hvo⟩ := bindBlock_success point selectors d2 opened 32#usize
      public1.change (by decide) hpoint hbox hc2 hopened hc
    refine ⟨out, ?_, hco, ?_⟩
    · unfold fixedPrefix
      rw [h1]
      simp only [bind_tc_ok]
      rw [h2]
      simp only [bind_tc_ok, hrec]
      exact ho
    · rw [model]
      simp only [hrec]
      have hm : decoded out = step point opened 32 public1.change (decoded d2) := by
        unfold step
        exact funext hvo
      rw [h2m] at hm
      exact hm
  | some recipient =>
    obtain ⟨d3, h3, hc3, hv3⟩ := bindBlock_success point selectors d2 opened 29#usize
      recipient (by decide) hpoint hbox hc2 hopened (hr recipient hrec)
    have h3m : decoded d3 = step point opened 29 recipient (decoded d2) := by
      unfold step
      exact funext hv3
    rw [h2m] at h3m
    obtain ⟨out, ho, hco, hvo⟩ := bindBlock_success point selectors d3 opened 32#usize
      public1.change (by decide) hpoint hbox hc3 hopened hc
    refine ⟨out, ?_, hco, ?_⟩
    · unfold fixedPrefix
      rw [h1]
      simp only [bind_tc_ok]
      rw [h2]
      simp only [bind_tc_ok, hrec]
      rw [h3]
      simp only [bind_tc_ok]
      exact ho
    · rw [model]
      simp only [hrec]
      have hm : decoded out = step point opened 32 public1.change (decoded d3) := by
        unfold step
        exact funext hvo
      rw [h3m] at hm
      exact hm

#print axioms zero_canonical
#print axioms zero_decoded
#print axioms source_success
end
end AspisR1.DigestFixedPrefix
