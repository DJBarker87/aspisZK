import PoseidonInternalPairMaps
import PoseidonM31DotSevenExact

/-! Complete actual internal-pair caller: its three maps, both seven-input
dot products, and both internal rounds are composed at their checked source
boundaries. The result is the existing R0P internal-pair model. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInternalPairExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State QM Exact Decode Canonical CanonicalState cell)
open AspisR1.PoseidonInternalPairMaps
open AspisR1.PoseidonM31DotReads (sliceCell)

def constantModel (local1 : State) (parity : Nat) (hp : parity ≤ 1) : Exact :=
  (List.ofFn (fun i : Fin 7 => Decode (cell local1 ⟨i.val+2,by
      have hi := i.isLt
      have h16 : (16#usize).val = 16 := by scalar_tac
      rw [h16]
      omega⟩) *
    R0P.poseidonInternalConstants (⟨2*i.val+parity,by have hi := i.isLt; omega⟩ : Fin 14))).foldl (·+·) 0

theorem dot_source (local1 : State) (hc : CanonicalState local1) (parity : Nat) (hp : parity ≤ 1) :
    ∃ out : QM,
      field.qm31_m31_dot (Array.to_slice (weights local1)) (Array.to_slice (constants parity)) = .ok out ∧
      Canonical out ∧ Decode out = constantModel local1 parity hp := by
  have hwlen : (Array.to_slice (weights local1)).val.length = 7 := (weights local1).property
  have hvlen : (Array.to_slice (constants parity)).val.length = 7 := (constants parity).property
  obtain ⟨out,hrun,hcanonical,hmodel⟩ := AspisR1.PoseidonM31DotSevenExact.source_success
    (Array.to_slice (weights local1)) (Array.to_slice (constants parity))
    hwlen hvlen (weights_canonical local1 hc) (constants_canonical parity)
  have hterms (i : Fin 7) :
      Decode (sliceCell (Array.to_slice (weights local1)) i.val (by rw [hwlen]; exact i.isLt)) *
        ((sliceCell (Array.to_slice (constants parity)) i.val (by rw [hvlen]; exact i.isLt)).val : Exact) =
      Decode (cell local1 ⟨i.val+2,by
          have hi := i.isLt
          have h16 : (16#usize).val = 16 := by scalar_tac
          rw [h16]
          omega⟩) *
        R0P.poseidonInternalConstants (⟨2*i.val+parity,by have hi := i.isLt; omega⟩ : Fin 14) := by
    change Decode (cell (weights local1) i) * ((cell (constants parity) i).val : Exact) = _
    rw [weights_model,constants_model parity hp,AspisR1.PoseidonRemainingConstantsExact.internal_model]
  refine ⟨out,hrun,hcanonical,?_⟩
  exact hmodel.trans (congrArg (fun xs : List Exact => xs.foldl (·+·) 0)
    (congrArg List.ofFn (funext hterms)))

theorem source_success (state local1 : State) (hstate : CanonicalState state)
    (hlocal : CanonicalState local1) :
    ∃ out : State, state_only_poseidon.interpolated_internal_pair state local1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16,
        Decode (cell out j) = R0P.poseidonInterpolatedInternalPair
          (fun i => Decode (cell state i)) (fun i => Decode (cell local1 i)) j := by
  obtain ⟨even,heven,hceven,hmeven⟩ := dot_source local1 hlocal 0 (by decide)
  obtain ⟨odd,hodd,hcodd,hmodd⟩ := dot_source local1 hlocal 1 (by decide)
  obtain ⟨middle,hmiddle,hcmiddle,hmmiddle⟩ :=
    AspisR1.PoseidonInternalRoundExact.source_success state even hstate hceven
  obtain ⟨out,hout,hcout,hmout⟩ :=
    AspisR1.PoseidonInternalRoundExact.source_success middle odd hcmiddle hcodd
  refine ⟨out,?_,hcout,?_⟩
  · simp only [state_only_poseidon.interpolated_internal_pair,weights_source,even_source,odd_source,
      lift,bind_tc_ok,heven,hodd,hmiddle,hout]
  · have hmid : (fun i : Fin 16 => Decode (cell middle i)) =
        (fun i : Fin 16 => R0P.poseidonInternalRound
          (fun k : Fin 16 => Decode (cell state k)) (Decode even) i) := by
      funext i
      exact hmmiddle i
    intro j
    change Decode (cell out j) = R0P.poseidonInterpolatedInternalPair
      (fun i : Fin 16 => Decode (cell state i)) (fun i : Fin 16 => Decode (cell local1 i)) j
    rw [hmout j, hmid, hmeven, hmodd]
    rfl

#print axioms dot_source
#print axioms source_success
end AspisR1.PoseidonInternalPairExact
