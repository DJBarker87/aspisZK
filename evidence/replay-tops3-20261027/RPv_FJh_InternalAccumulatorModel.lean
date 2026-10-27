import RPv_FJh_InternalAccumulateState
import RPv_RawPoseidonRowField
import ExtractedMaskQM31Exact

/-! Symbolic interpretation of the actual nonzero-lane accumulator. The
four-coordinate decoder is additive; no concrete fifteen-lane term or tower
multiplication is reduced. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalAccumulatorModel
open Aeneas Aeneas.Std Result
open AspisR1.FJh_Base (State QM Exact Decode cell CanonicalState)
open AspisR1.FJh_InternalStateWords
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.RawPoseidonRowField (decodeWords decodeWords_add)
open AspisV8R17.RawReducer (P)

theorem wordVec_decode (q : QM) :
    decodeWords (fun j => (cell (wordVec q) j).val) = Decode q := by
  rfl

theorem wordNat_decode (state : State) (lane : Fin 16) :
    decodeWords (fun j => wordNat state lane.val j) = Decode (cell state lane) := by
  have hwords : (fun j : Fin 4 => wordNat state lane.val j) =
      (fun j => (cell (wordVec (cell state lane)) j).val) := by
    funext j
    unfold wordNat
    rw [List.getElem?_eq_getElem (by simpa [state.property] using lane.isLt)]
    rfl
  rw [hwords]
  exact wordVec_decode (cell state lane)

theorem remaining_decode_eq_sum (state : State) (start fuel : Nat) :
    decodeWords (fun j => remaining state start fuel j) =
      (List.ofFn (fun i : Fin fuel =>
        decodeWords (fun j => wordNat state (start+i.val) j))).sum := by
  induction fuel generalizing start with
  | zero =>
    change decodeWords (fun _ => 0) = _
    simp only [List.ofFn_zero,List.sum_nil]
    ext <;> simp [decodeWords]
  | succ fuel ih =>
    change decodeWords (fun j => wordNat state start j + remaining state (start+1) fuel j) = _
    rw [decodeWords_add,ih,List.ofFn_succ,List.sum_cons]
    have htail : (fun i : Fin fuel => decodeWords (fun j => wordNat state (start+1+i.val) j)) =
        (fun i : Fin fuel => decodeWords (fun j => wordNat state (start+i.succ.val) j)) := by
      funext i
      have hi : start+1+i.val = start+i.succ.val := by
        change start+1+i.val = start+(i.val+1)
        omega
      rw [hi]
    simpa only [Fin.val_zero,Nat.add_zero,htail]

def partSum (state : State) : Exact :=
  (List.ofFn (fun i : Fin 15 => Decode (cell state i.succ))).foldl (· + ·) 0

theorem source_success (state : State) (hstate : CanonicalState state) :
    ∃ out : Raw4,
      FIq_Native.state_only_poseidon.internal_linear_lazy_loop0 state
        AspisR1.FJh_InternalAccumulateState.zero 1#usize = .ok out ∧
      RawBound out (15*P) ∧
      decodeWords (fun j => (cell out j).val) = partSum state := by
  obtain ⟨out,hrun,hbound,hvalues⟩ :=
    AspisR1.FJh_InternalAccumulateState.source_success state hstate
  refine ⟨out,hrun,hbound,?_⟩
  have hfun : (fun j : Fin 4 => (cell out j).val) =
      (fun j => remaining state 1 15 j) := funext hvalues
  rw [hfun,remaining_decode_eq_sum]
  have hterms : (fun i : Fin 15 => decodeWords (fun j => wordNat state (1+i.val) j)) =
      (fun i : Fin 15 => Decode (cell state i.succ)) := by
    funext i
    have hi : 1+i.val = i.succ.val := by
      change 1+i.val = i.val+1
      omega
    rw [hi,wordNat_decode]
  rw [hterms,List.sum_eq_foldl]
  rfl

#print axioms wordVec_decode
#print axioms wordNat_decode
#print axioms remaining_decode_eq_sum
#print axioms source_success
end AspisR1.FJh_InternalAccumulatorModel
