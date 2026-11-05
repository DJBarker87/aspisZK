import NIH_ExternalLazy
import NIH_ExternalPacked
import NDO_JGj_QmRoundTotal
import NDO_JGj_M31RoundTotal
import RPv_FJb_QmLazyRound
import RPv_FJb_M31LazyRound
import RPv_FJe_QmPackedNonlinear
import RPv_FJe_M31PackedNonlinear
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_FullRounds
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FIq_Native.state_only_poseidon
abbrev State := Array NQ 16#usize
abbrev BaseConstants := FJb_M31Step.Constants
abbrev baseValue (constants : BaseConstants) : Fin 16→FIv_NativeValue.K :=
 fun j=>((FJb_TailCell.cell constants j).val : FIv_NativeValue.K)
theorem qm (s c : State) (hs : canonical s) (hc : canonical c) :
 ∃ out,full_round s c=ok out ∧ canonical out ∧
 decoded out=R0P.poseidonFullRound (decoded s) (decoded c) := by
 obtain ⟨out,run,_⟩:=JGj_QmRoundTotal.lazy s c hs hc
 exact ⟨out,run,FJb_QmLazyRound.value s c out hs hc run⟩
theorem m31 (s : State) (c : BaseConstants) (hs : canonical s) (hc : FJb_M31Step.Bounded c) :
 ∃ out,full_round_m31_constants s c=ok out ∧ canonical out ∧
 decoded out=R0P.poseidonFullRound (decoded s) (baseValue c) := by
 obtain ⟨out,run,_⟩:=JGj_M31RoundTotal.lazy s c hs hc
 exact ⟨out,run,FJb_M31LazyRound.value s out c hs hc run⟩
theorem packed_qm (s c : State) (hs : canonical s) (hc : canonical c) :
 ∃ out,full_round_packed s c=ok out ∧ canonical out ∧
 decoded out=fun g=>R0P.poseidonPackingFormula
  ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
  (fun j=>R0P.poseidonFullRound (decoded s) (decoded c) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨out,run,canon⟩:=JGj_QmRoundTotal.packed s c hs hc
 obtain ⟨nonlinear,nc,nv,call⟩:=FJe_QmPackedNonlinear.value s c out hs hc run
 have external:=FJe_ExternalPackedValue.value nonlinear out nc call
 refine ⟨out,run,canon,?_⟩
 rw [external.2,nv]
 rfl
theorem packed_m31 (s : State) (c : BaseConstants) (hs : canonical s) (hc : FJb_M31Step.Bounded c) :
 ∃ out,full_round_m31_constants_packed s c=ok out ∧ canonical out ∧
 decoded out=fun g=>R0P.poseidonPackingFormula
  ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
  (fun j=>R0P.poseidonFullRound (decoded s) (baseValue c) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨out,run,canon⟩:=JGj_M31RoundTotal.packed s c hs hc
 obtain ⟨nonlinear,nc,nv,call⟩:=FJe_M31PackedNonlinear.value s c out hs hc run
 have external:=FJe_ExternalPackedValue.value nonlinear out nc call
 refine ⟨out,run,canon,?_⟩
 rw [external.2,nv]
 rfl
#print axioms qm
#print axioms m31
#print axioms packed_qm
#print axioms packed_m31
end AspisR1.NIH_FullRounds
end
