import PoseidonInterpolatedFullInputs
import PoseidonFullRoundLazyExact
import PoseidonFullRoundPackedExact

/-! Source-level success/model theorem for the actual interpolated full-pair
    wrapper. It composes the proven preparation with the actual lazy then
    packed full-round callers; no intermediate success is assumed. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInterpolatedFullPairExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonExternalPackedGroupCall (Packed packedCell packedCanonical)
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisR1.PoseidonExternalPackedModel (lane)

abbrev State := Array field.QM31 16#usize
abbrev CanonicalState := AspisR1.PoseidonFullRoundCellStep.CanonicalState
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact

private theorem bind_ok_pair {A B C : Type} (a : A) (b : B)
    (k : A → B → Result C) :
    (do let (x, y) ← (Result.ok (a, b) : Result (A × B)); k x y) = k a b := by
  rfl

private theorem bind_ok {A B : Type} (a : A) (k : A → Result B) :
    (do let x ← (Result.ok a : Result A); k x) = k a := by
  rfl

def decodedState (s : State) : Fin 16 → Exact := fun i => Decode (cell s i)

theorem qm_source_success (state local1 : State)
    (hstate : CanonicalState state) (hlocal : CanonicalState local1) :
    ∃ out : Packed,
      state_only_poseidon.interpolated_full_pair_packed state local1 = .ok out ∧
      packedCanonical out ∧
      ∀ group : Fin 4, Decode (packedCell out group) =
        R0P.poseidonPackingFormula iBasis uBasis (fun j =>
          R0P.poseidonInterpolatedFullPair (decodedState state) (decodedState local1)
            (lane group j)) := by
  obtain ⟨even, odd, hprepare, hcanEven, hcanOdd, hevenModel, hoddModel⟩ :=
    AspisR1.PoseidonInterpolatedFullInputs.prepare_success local1 hlocal
  obtain ⟨state1, hfirst, hcanState1, hfirstModel⟩ :=
    AspisR1.PoseidonFullRoundLazyExact.qm_source_success state even hstate hcanEven
  obtain ⟨out, hsecond, hcanOut, hsecondModel⟩ :=
    AspisR1.PoseidonFullRoundPackedExact.qm_source_success state1 odd hcanState1 hcanOdd
  have hevenState : decodedState even =
      fun i => AspisR1.PoseidonInterpolatedFullInputs.evenModel local1 i := by
    funext i
    exact hevenModel i
  have hoddState : decodedState odd =
      fun i => AspisR1.PoseidonInterpolatedFullInputs.oddModel local1 i := by
    funext i
    exact hoddModel i
  have hstate1Model : decodedState state1 =
      fun i => R0P.poseidonFullRound (decodedState state)
        (fun j => AspisR1.PoseidonInterpolatedFullInputs.evenModel local1 j) i := by
    funext i
    have h := hfirstModel i
    change Decode (cell state1 i) =
      R0P.poseidonFullRound (decodedState state) (decodedState even) i at h
    rw [hevenState] at h
    exact h
  have hinterpModel : R0P.poseidonInterpolatedFullPair
      (decodedState state) (decodedState local1) =
      (fun i => R0P.poseidonFullRound
        (fun k => R0P.poseidonFullRound (decodedState state)
          (fun j => AspisR1.PoseidonInterpolatedFullInputs.evenModel local1 j) k)
        (fun j => AspisR1.PoseidonInterpolatedFullInputs.oddModel local1 j) i) := by
    funext i
    rfl
  refine ⟨out, ?_, hcanOut, ?_⟩
  · rw [AspisR1.PoseidonInterpolatedFullInputs.wrapper_factor]
    rw [hprepare]
    rw [bind_ok_pair]
    rw [hfirst]
    rw [bind_ok]
    rw [hsecond]
  · intro group
    have h := hsecondModel group
    change Decode (packedCell out group) = R0P.poseidonPackingFormula iBasis uBasis
      (fun j => R0P.poseidonFullRound (decodedState state1) (decodedState odd)
        (lane group j)) at h
    rw [hstate1Model, hoddState] at h
    simpa only [hinterpModel] using h

#print axioms qm_source_success
end AspisR1.PoseidonInterpolatedFullPairExact
