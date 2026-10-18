import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import ArrayFromFnCopyStable
import RawPoseidonExternalAllRows
import RawPoseidonExtensionWords
import EmptyRootExecution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalPackedCallbackSource

open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowClosure
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonExternalRowWrapper
open AspisR1.RawPoseidonExternalAllRows

abbrev Input := AspisR1.RawPoseidonExternalRowClosure.Input

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

private def toUsize4 (i : Fin 4) : Usize :=
  Usize.ofNatCore i.val (small_nat_usize i.val i.isLt)

private theorem toUsize4_val (i : Fin 4) : (toUsize4 i).val = i.val := by
  simp [toUsize4, UScalar.ofNatCore_val_eq]

private theorem toUsize4_eq (i : Fin 4) (x : Usize) (hx : x.val = i.val) :
    toUsize4 i = x := by
  apply UScalar.eq_of_val_eq
  simp [toUsize4_val, hx]

/-- The per-output raw U64 value already used by the exact generated lazy-row
callback proof. The local packed callback has the same four checked source
branches, with the packed call's row array as its capture. -/
def rawRowFormula (input : Input) (output : Fin 4) (limb : Usize)
    (hlimb : limb.val < 4) : Nat :=
  AspisR1.RawPoseidonExternalRows.rawRowNat
    (fun r : Fin 4 => (limbValue input r limb hlimb).val) output

private theorem rawRowFormula_bound (input : Input) (output : Fin 4)
    (limb : Usize) (hlimb : limb.val < 4) : rawRowFormula input output limb hlimb < 2^35 := by
  apply AspisR1.RawPoseidonExternalRows.rawRowNat_lt_two_pow_35
  intro r
  exact (limbValue input r limb hlimb).bv.isLt

private theorem local_callback_value
    (input : Input) (output : Fin 4) (limb : Usize) (hlimb : limb.val < 4) :
    ∃ z : U64,
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, toUsize4 output) limb = .ok (z, (input, toUsize4 output)) ∧
      z.val = rawRowFormula input output limb hlimb := by
  obtain ⟨z0, z1, z2, z3, hc0, hv0, hc1, hv1, hc2, hv2, hc3, hv3⟩ :=
    call_mut_all_lanes_of_array_bounds input limb hlimb
  have hc0' : state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 0#usize) limb = .ok (z0, (input, 0#usize)) := by
    change state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 0#usize) limb = .ok (z0, (input, 0#usize))
    exact hc0
  have hc1' : state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 1#usize) limb = .ok (z1, (input, 1#usize)) := by
    change state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 1#usize) limb = .ok (z1, (input, 1#usize))
    exact hc1
  have hc2' : state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 2#usize) limb = .ok (z2, (input, 2#usize)) := by
    change state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 2#usize) limb = .ok (z2, (input, 2#usize))
    exact hc2
  have hc3' : state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 3#usize) limb = .ok (z3, (input, 3#usize)) := by
    change state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (input, 3#usize) limb = .ok (z3, (input, 3#usize))
    exact hc3
  fin_cases output
  · have ho : toUsize4 (⟨0, by decide⟩ : Fin 4) = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z0, ?_, ?_⟩
    · rw [ho]
      exact hc0'
    · simpa [rawRowFormula, AspisR1.RawPoseidonExternalRows.rawRowNat,
        RawPoseidonExternalRowReads.rawRowNat] using hv0
  · have ho : toUsize4 (⟨1, by decide⟩ : Fin 4) = 1#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z1, ?_, ?_⟩
    · rw [ho]
      exact hc1'
    · simpa [rawRowFormula, AspisR1.RawPoseidonExternalRows.rawRowNat,
        RawPoseidonExternalRowReads.rawRowNat] using hv1
  · have ho : toUsize4 (⟨2, by decide⟩ : Fin 4) = 2#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z2, ?_, ?_⟩
    · rw [ho]
      exact hc2'
    · simpa [rawRowFormula, AspisR1.RawPoseidonExternalRows.rawRowNat,
        RawPoseidonExternalRowReads.rawRowNat] using hv2
  · have ho : toUsize4 (⟨3, by decide⟩ : Fin 4) = 3#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z3, ?_, ?_⟩
    · rw [ho]
      exact hc3'
    · simpa [rawRowFormula, AspisR1.RawPoseidonExternalRows.rawRowNat,
        RawPoseidonExternalRowReads.rawRowNat] using hv3

private def callbackValue (input : Input) (output : Fin 4) (n : Nat) : U64 :=
  if hn : n < 4 then
    let limb := toUsize4 ⟨n, hn⟩
    let hl : limb.val < 4 := by simpa [limb, toUsize4_val] using hn
    U64.ofNatCore (rawRowFormula input output limb hl) (by
      have h := rawRowFormula_bound input output limb hl
      simp only [UScalarTy.U64_numBits_eq]
      omega)
  else 0#u64

/-- Exact source `array_from_fn_copy` success for one local external row.
This is the actual U64 callback in `external_local_packed_raw`, not an
assumed result array. Each output cell retains the row formula used by the
existing raw Poseidon row theorem. -/
theorem local_row_from_fn_success (input : Input) (output : Fin 4) :
    ∃ raw : Array U64 4#usize,
      array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (input, toUsize4 output) = .ok raw ∧
      ∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          rawRowFormula input output (toUsize4 j)
            (by simpa [toUsize4_val] using j.isLt) := by
  let inst := state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  let value : Nat → U64 := callbackValue input output
  have hstable : ∀ i : Usize, i.val < 4 →
      inst.call_mut (input, toUsize4 output) i = .ok (value i.val, (input, toUsize4 output)) := by
    intro i hi
    let ix : Fin 4 := ⟨i.val, hi⟩
    have hix : toUsize4 ix = i := toUsize4_eq ix i rfl
    obtain ⟨z, hcall, hz⟩ := local_callback_value input output i hi
    have hv : value i.val = z := by
      dsimp [value, callbackValue]
      rw [dif_pos hi]
      apply UScalar.eq_of_val_eq
      have hz' : rawRowFormula input output (toUsize4 ix)
          (by simpa [toUsize4_val] using hi) = z.val := by
        simpa only [hix] using hz.symm
      simpa only [U64.ofNatCore_val_eq] using hz'
    simpa [inst, hv] using hcall
  obtain ⟨raw, hrun, hcells⟩ :=
    AspisR1SelectedMaskProbe.array_from_fn_copy_stable
      (4#usize) core.marker.CopyU64 inst 0#u64 (input, toUsize4 output)
      value hstable
  refine ⟨raw, hrun, ?_⟩
  intro j
  have hj : j.val < 4 := j.isLt
  have hout := hcells j.val (by simpa using hj)
  have hvalue : value j.val =
      U64.ofNatCore (rawRowFormula input output (toUsize4 j)
        (by simpa [toUsize4_val] using hj)) (by
          have h := rawRowFormula_bound input output (toUsize4 j)
            (by simpa [toUsize4_val] using hj)
          simp only [UScalarTy.U64_numBits_eq]
          omega) := by
    dsimp [value, callbackValue]
    rw [dif_pos hj]
  rw [hvalue] at hout
  have hval := congrArg UScalar.val hout
  simpa only [U64.ofNatCore_val_eq] using hval


open AspisV8R19.TraversalRuntime

private def limbsOf (q : field.QM31) : Array Std.U32 4#usize :=
  Array.make 4#usize [q.c0.a, q.c0.b, q.c1.a, q.c1.b]

private def mapInput (input : Array field.QM31 4#usize) :
    Array (Array Std.U32 4#usize) 4#usize :=
  ⟨input.val.map limbsOf, by simpa [input.property]⟩

private theorem mapState_extension_limbs (xs : List field.QM31) :
    mapState (BuiltinFnMut field.QM31 (Array Std.U32 4#usize)).call_mut
      xs state_only_poseidon.extension_limbs =
        .ok (xs.map limbsOf, state_only_poseidon.extension_limbs) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
      have hcall : (BuiltinFnMut field.QM31 (Array Std.U32 4#usize)).call_mut
          state_only_poseidon.extension_limbs q =
            .ok (limbsOf q, state_only_poseidon.extension_limbs) := by
        simp [BuiltinFnMut, AspisR1.RawPoseidonExtensionWords.extension_limbs_words,
          limbsOf]
      simp only [mapState, hcall, bind_tc_ok, ih]

theorem extension_limbs_array_map_success
    (input : Array field.QM31 4#usize) :
    core.array.Array.map
      (BuiltinFnMut field.QM31 (Array Std.U32 4#usize)) input
      state_only_poseidon.extension_limbs = .ok (mapInput input) := by
  exact core.array.Array.map_success
    (BuiltinFnMut field.QM31 (Array Std.U32 4#usize)) input
    state_only_poseidon.extension_limbs (input.val.map limbsOf)
    state_only_poseidon.extension_limbs (mapState_extension_limbs input.val)

/-- The actual map then four from_fn rows in `external_local_packed_raw`.
The callback source arrays and each row's four exact U64 outputs are retained. -/
theorem mapped_local_rows_success (input : Array field.QM31 4#usize) :
    ∃ rawInput : Array (Array Std.U32 4#usize) 4#usize,
      core.array.Array.map
        (BuiltinFnMut field.QM31 (Array Std.U32 4#usize)) input
        state_only_poseidon.extension_limbs = .ok rawInput ∧
      ∀ output : Fin 4, ∃ rawRow : Array U64 4#usize,
        array_from_fn_copy 4#usize core.marker.CopyU64
          state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
          0#u64 (rawInput, toUsize4 output) = .ok rawRow ∧
        ∀ j : Fin 4,
          (rawRow.val[j.val]'(by simpa [rawRow.property] using j.isLt)).val =
            rawRowFormula rawInput output (toUsize4 j)
              (by simpa [toUsize4_val] using j.isLt) := by
  refine ⟨mapInput input, extension_limbs_array_map_success input, ?_⟩
  intro output
  exact local_row_from_fn_success (mapInput input) output

#print axioms mapState_extension_limbs
#print axioms extension_limbs_array_map_success
#print axioms mapped_local_rows_success

#print axioms local_callback_value
#print axioms local_row_from_fn_success
end AspisR1.PoseidonExternalLocalPackedCallbackSource
