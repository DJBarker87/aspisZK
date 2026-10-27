import RPv_FJh_InternalShiftCallEquation
import RPv_FJh_InternalClosureSums

/-! Exact source callback for nonzero internal-linear lanes. All checked
reads, index subtraction, shift and addition are derived; capture is stable. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalShiftClosure
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalClosureSums (Raw4 Words4 RawBound CanonicalWords)
open AspisR1.FJh_InternalWordOps (wide wide_value)
open AspisR1.ExtractedMaskReducerOps AspisV8R17.RawReducer

theorem source_success (full : Raw4) (words : Words4) (lane limb : Usize)
    (hlane : 1 ≤ lane.val) (hlaneEnd : lane.val < 16) (hlimb : limb.val < 4)
    (hfull : RawBound full (16*P)) (hwords : CanonicalWords words) :
    ∃ out : U64,
      state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (full,words,lane) limb = .ok (out,(full,words,lane)) ∧
      out.val = (cell full (⟨limb.val,hlimb⟩ : Fin 4)).val +
        (cell words (⟨limb.val,hlimb⟩ : Fin 4)).val *
          2 ^ R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) ∧ out.val < 2^48 := by
  let index : Fin 4 := ⟨limb.val,hlimb⟩
  let p := cell full index
  let w := cell words index
  have hb : limb.val < (4#usize).val := by simpa using hlimb
  have hreadP : Array.index_usize full limb = .ok p := by
    simpa only [p,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok full limb hb
  have hreadW : Array.index_usize words limb = .ok w := by
    simpa only [w,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok words limb hb
  have hone : (1#usize).val = 1 := by decide
  obtain ⟨offset,hsub,hoffset⟩ := sub_success lane 1#usize (by rw [hone]; exact hlane)
  rw [hone] at hoffset
  have ho : offset.val < 15 := by omega
  let shift := AspisR1.FJh_InternalShiftsExact.shift (⟨offset.val,ho⟩ : Fin 15)
  have hreadShift : Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS offset = .ok shift :=
    AspisR1.FJh_InternalShiftsExact.source_read offset ho
  have hshiftBound : shift.val ≤ 16 := AspisR1.FJh_InternalShiftsExact.bounded _
  have hshiftModel : shift.val = R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) := by
    have hm := AspisR1.FJh_InternalShiftsExact.model (⟨offset.val,ho⟩ : Fin 15)
    have hindex : (⟨offset.val,ho⟩ : Fin 15) = (⟨lane.val-1,by omega⟩ : Fin 15) := Fin.ext hoffset
    exact hm.trans (congrArg R0P.poseidonInternalShifts hindex)
  have hw : w.val < P := hwords index
  have hp : p.val < 16*P := hfull index
  obtain ⟨shifted,hshiftRun,hshiftValue,hshiftSmall⟩ :=
    AspisR1.FJh_InternalWordOps.shifted_word_success w shift hw hshiftBound
  have hlimit : 16*P + 2^47 < 2^48 := by norm_num [P]
  have hsum : p.val+shifted.val < 2^48 := by omega
  obtain ⟨out,hadd,hout⟩ := add_success p shifted (by omega)
  have hvalue : out.val = p.val + w.val * 2 ^ R0P.poseidonInternalShifts
      (⟨lane.val-1,by omega⟩ : Fin 15) := by rw [hout,hshiftValue,hshiftModel]
  refine ⟨out,?_,hvalue,by rw [hout]; exact hsum⟩
  rw [AspisR1.FJh_InternalShiftCallEquation.source_eq]
  simp only [hreadP,hreadW,hsub,hreadShift,hshiftRun,hadd,bind_tc_ok]

#print axioms source_success
end AspisR1.FJh_InternalShiftClosure
