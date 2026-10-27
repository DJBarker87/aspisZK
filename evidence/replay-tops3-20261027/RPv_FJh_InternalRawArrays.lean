import RPv_FJh_Raw4Constructor
import RPv_FJh_InternalShiftClosure

/-! Actual stable Copy-array construction for each internal-linear callback.
All four raw output values and bounds are retained for reconstruction. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalRawArrays
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalClosureSums
open AspisV8R17.RawReducer (P)

abbrev FullCallback := state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev ZeroCallback := state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev ShiftCallback := state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64

theorem full_source (part : Raw4) (old : Words4)
    (hp : RawBound part (15*P)) (ho : CanonicalWords old) :
    ∃ out : Raw4,
      array_from_fn_copy 4#usize core.marker.CopyU64 FullCallback 0#u64 (part,old) = .ok out ∧
      RawBound out (16*P) ∧ ∀ j : Fin 4,
        (cell out j).val = (cell part j).val + (cell old j).val := by
  obtain ⟨out,hrun,hprops⟩ := AspisR1.FJh_Raw4Constructor.source_success FullCallback (part,old)
    (fun j v => v.val = (cell part j).val + (cell old j).val ∧ v.val < 16*P)
    (by intro i hi; exact full_sum_call part old i hi hp ho)
  exact ⟨out,hrun,(fun j => (hprops j).2),(fun j => (hprops j).1)⟩

theorem zero_source (part : Raw4) (old : Words4)
    (hp : RawBound part (16*P)) (ho : CanonicalWords old) :
    ∃ out : Raw4,
      array_from_fn_copy 4#usize core.marker.CopyU64 ZeroCallback 0#u64 (part,old) = .ok out ∧
      RawBound out (17*P) ∧ ∀ j : Fin 4,
        (cell out j).val = (cell part j).val + P - (cell old j).val := by
  obtain ⟨out,hrun,hprops⟩ := AspisR1.FJh_Raw4Constructor.source_success ZeroCallback (part,old)
    (fun j v => v.val = (cell part j).val + P - (cell old j).val ∧ v.val < 17*P)
    (by intro i hi; exact zero_sum_call part old i hi hp ho)
  exact ⟨out,hrun,(fun j => (hprops j).2),(fun j => (hprops j).1)⟩

theorem shift_source (full : Raw4) (words : Words4) (lane : Usize)
    (hlane : 1 ≤ lane.val) (hlaneEnd : lane.val < 16)
    (hf : RawBound full (16*P)) (hw : CanonicalWords words) :
    ∃ out : Raw4,
      array_from_fn_copy 4#usize core.marker.CopyU64 ShiftCallback 0#u64 (full,words,lane) = .ok out ∧
      RawBound out (2^48) ∧ ∀ j : Fin 4,
        (cell out j).val = (cell full j).val + (cell words j).val *
          2 ^ R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) := by
  obtain ⟨out,hrun,hprops⟩ := AspisR1.FJh_Raw4Constructor.source_success ShiftCallback (full,words,lane)
    (fun j v => v.val = (cell full j).val + (cell words j).val *
      2 ^ R0P.poseidonInternalShifts (⟨lane.val-1,by omega⟩ : Fin 15) ∧ v.val < 2^48)
    (by intro i hi; exact AspisR1.FJh_InternalShiftClosure.source_success full words lane i hlane hlaneEnd hi hf hw)
  exact ⟨out,hrun,(fun j => (hprops j).2),(fun j => (hprops j).1)⟩

#print axioms full_source
#print axioms zero_source
#print axioms shift_source
end AspisR1.FJh_InternalRawArrays
