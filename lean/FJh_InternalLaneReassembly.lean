import FJh_InternalRawArrays
import FJh_InternalAccumulatorModel
import FJh_RawLimbReassembly

/-! Decode the actual reconstructed zero and nonzero internal-linear lanes.
Raw arithmetic is kept separate from exact-field algebra. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalLaneReassembly
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (QM Exact Decode Canonical cell)
open AspisR1.FJh_InternalClosureSums (Raw4 Words4 RawBound CanonicalWords)
open AspisR1.FJh_InternalStateWords (wordVec wordVec_canonical)
open AspisR1.FJh_InternalAccumulatorModel (wordVec_decode)
open AspisR1.FJh_InternalRawArrays
open AspisR1.RawPoseidonRowField
open AspisV8R17.RawReducer (P)

abbrev rawDecode (a : Raw4) : Exact := decodeWords (fun j => (cell a j).val)

def zeroRun (part : Raw4) (old : QM) : Result QM := do
  let a ← array_from_fn_copy 4#usize core.marker.CopyU64 ZeroCallback 0#u64 (part,wordVec old)
  state_only_poseidon.extension_from_raw_limbs a

def shiftRun (full : Raw4) (q : QM) (lane : Usize) : Result QM := do
  let a ← array_from_fn_copy 4#usize core.marker.CopyU64 ShiftCallback 0#u64 (full,wordVec q,lane)
  state_only_poseidon.extension_from_raw_limbs a

theorem zero_source (part : Raw4) (old : QM)
    (hp : RawBound part (16*P)) (ho : Canonical old) :
    ∃ out : QM, zeroRun part old = .ok out ∧ Canonical out ∧
      Decode out = rawDecode part - Decode old := by
  have hw := wordVec_canonical old ho
  obtain ⟨raw,hrun,_,hvalues⟩ := AspisR1.FJh_InternalRawArrays.zero_source part (wordVec old) hp hw
  obtain ⟨out,hreassemble,hcan,hdecode⟩ := AspisR1.FJh_RawLimbReassembly.source_success raw
  change Decode out = rawDecode raw at hdecode
  have hfields : ∀ j : Fin 4,
      ((cell raw j).val : AspisV8R15.ExactTowerBase.M31Exact) =
        ((cell part j).val : AspisV8R15.ExactTowerBase.M31Exact) -
        ((cell (wordVec old) j).val : AspisV8R15.ExactTowerBase.M31Exact) := by
    intro j
    exact AspisR1.FJh_InternalWordOps.zeroSubtract_model (cell part j)
      (cell (wordVec old) j) (cell raw j) (hw j) (hvalues j)
  have hmodel : rawDecode raw = rawDecode part - decodeWords (fun j => (cell (wordVec old) j).val) := by
    ext <;> first | exact hfields 0 | exact hfields 1 | exact hfields 2 | exact hfields 3
  rw [wordVec_decode] at hmodel
  refine ⟨out,?_,hcan,hdecode.trans hmodel⟩
  simp only [zeroRun,hrun,hreassemble,bind_tc_ok]

theorem shift_source (full : Raw4) (q : QM) (lane : Usize)
    (hlane : 1 ≤ lane.val) (hend : lane.val < 16)
    (hf : RawBound full (16*P)) (hq : Canonical q) :
    ∃ out : QM, shiftRun full q lane = .ok out ∧ Canonical out ∧
      Decode out = rawDecode full + Decode q *
        ((1 <<< R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) : Nat) : Exact) := by
  have hw := wordVec_canonical q hq
  obtain ⟨raw,hrun,_,hvalues⟩ := AspisR1.FJh_InternalRawArrays.shift_source
    full (wordVec q) lane hlane hend hf hw
  obtain ⟨out,hreassemble,hcan,hdecode⟩ := AspisR1.FJh_RawLimbReassembly.source_success raw
  change Decode out = rawDecode raw at hdecode
  let n := 2 ^ R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15)
  have hfun : (fun j : Fin 4 => (cell raw j).val) =
      (fun j => (cell full j).val + n*(cell (wordVec q) j).val) := by
    funext j
    rw [hvalues j]
    exact congrArg ((cell full j).val + ·) (Nat.mul_comm _ _)
  have hmodel : rawDecode raw = rawDecode full + (n : Exact) * Decode q := by
    have ha := decodeWords_add (fun j : Fin 4 => (cell full j).val)
      (fun j : Fin 4 => n * (cell (wordVec q) j).val)
    have hm := decodeWords_nat_mul n (fun j : Fin 4 => (cell (wordVec q) j).val)
    have hqdecode := wordVec_decode q
    exact (congrArg decodeWords hfun).trans
      (ha.trans (congrArg (rawDecode full + ·)
        (hm.trans (congrArg ((n : Exact) * ·) hqdecode))))
  have hn : (1 <<< R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) : Nat) = n := by
    rw [Nat.shiftLeft_eq,Nat.one_mul]
  refine ⟨out,?_,hcan,?_⟩
  · simp only [shiftRun,hrun,hreassemble,bind_tc_ok]
  · rw [hdecode,hmodel,hn,mul_comm (n : Exact)]

#print axioms zero_source
#print axioms shift_source
end AspisR1.FJh_InternalLaneReassembly
