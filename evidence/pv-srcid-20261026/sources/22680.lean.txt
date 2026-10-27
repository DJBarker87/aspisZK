import R1Z.PV_Src_Forest_DigestArguments

/-! The actual extracted compiler's value_bits helper, symbolically for all
raw machine words. No concrete bit-vector or hash table is enumerated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_NativeValueBits
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1

def bitAt (value : U32) (n : Nat) : U32 :=
  if hn : n < 30 then U32.wrapping_shr value
    (U32.ofNatCore n (by simp; omega)) &&& 1#u32 else 0#u32

theorem cast_index (i : Usize) (hi : i.val < 30) :
    UScalar.cast .U32 i = U32.ofNatCore i.val (by simp; omega) := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq,UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt (by simp [UScalar.size_def]; omega)

theorem helper (value : U32) : pair_trace.value_bits value =
    ok (BuilderRecordsArray.tabulate 30#usize (bitAt value)) := by
  unfold pair_trace.value_bits
  apply PV_Src_Forest_DigestArguments.from_fn_nat
  intro i hi
  change pair_trace.value_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut value i = _
  rw [pair_trace.value_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut]
  have hi' : i.val < 30 := by simpa using hi
  simp only [lift,bind_tc_ok,bitAt,dif_pos hi',cast_index i hi']

theorem bit_value (value : U32) (n : Nat) (hn : n < 30) :
    (bitAt value n).val = value.val / 2^n % 2 := by
  rw [bitAt,dif_pos hn,bit_val _ _ (by simp; omega)]
  simp only [UScalar.ofNatCore_val_eq]

theorem bit_boolean (value : U32) (n : Nat) (hn : n < 30) :
    (bitAt value n).val = 0 ∨ (bitAt value n).val = 1 := by
  rw [bit_value value n hn]
  have h := Nat.mod_lt (value.val / 2^n) (by decide : 0 < 2)
  omega

theorem cells (value : U32) : ∃ out, pair_trace.value_bits value = ok out ∧
    ∀ n, n < 30 → (out.val[n]!).val = value.val / 2^n % 2 := by
  refine ⟨BuilderRecordsArray.tabulate 30#usize (bitAt value),helper value,?_⟩
  intro n hn
  rw [BuilderRecordsArray.tabulate_get _ _ n (by simpa using hn)]
  exact bit_value value n hn

#print axioms cast_index
#print axioms helper
#print axioms bit_value
#print axioms bit_boolean
#print axioms cells
end R1Z.PV_Src_NativeValueBits
