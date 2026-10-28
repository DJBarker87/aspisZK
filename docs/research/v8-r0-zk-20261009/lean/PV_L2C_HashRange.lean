import PV_L2C_HashLoopRange
import R1Z.PV_Src_PortNodeDigest
set_option autoImplicit false
namespace PV_L2C_HashRange
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev callback := PV_L2C_HashLoopRange.callback

def initial (domain : U32) (input : Slice U32) : State :=
  ((Array.repeat 16#usize 0#u32).set 8#usize domain).set 9#usize
    (UScalar.cast .U32 (Slice.len input))

theorem initial_canonical (domain : U32) (input : Slice U32)
    (hd : domain.val < 2147483647) (hl : input.val.length < 2147483647) :
    Canonical (initial domain input) := by
  have hn : (UScalar.cast .U32 (Slice.len input)).val < 2147483647 := by
    rw [UScalar.cast_val_eq,Slice.len_val]
    change input.length % 4294967296 < 2147483647
    change input.length < 2147483647 at hl
    omega
  intro i
  unfold initial
  rw [BuilderRecordsArray.set_get _ _ _ _ (by decide),
    BuilderRecordsArray.set_get _ _ _ _ (by decide),rep16]
  split_ifs <;> first | exact hn | exact hd | decide
#print axioms initial_canonical

theorem digest (s : State) :
    core.array.from_fn 8#usize
      (poseidon2.hash_fields_with_trace.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31 callback) s =
      ok (digest8 s) := by
  have hf : ∀ i : Usize, i.val < 8 →
      (poseidon2.hash_fields_with_trace.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31 callback).call_mut s i =
      ok (s.val[i.val]!,s) := by
    intro i hi
    with_unfolding_all change (do let m ← Array.index_usize s i; ok (m,s)) = _
    rw [index_ok s i (by simp; omega)]
    rfl
  rw [PV_Src_Forest_DigestArguments.from_fn_nat 8#usize _ s (fun i => s.val[i]!) hf]
  rfl
#print axioms digest

theorem shape (domain : U32) (input : Slice U32) (hne : input.val ≠ []) :
    poseidon2.hash_fields domain input =
      (do
        let s ← poseidon2.hash_fields_with_trace_loop0 callback
          ⟨⟨input,8⟩,0#usize⟩ () (initial domain input)
        ok (digest8 s)) := by
  unfold poseidon2.hash_fields poseidon2.hash_fields_with_trace
  simp only [poseidon2.RATE,aspis_core.field.M31.ZERO]
  have hr : Usize.wrapping_add 8#usize 1#usize = 9#usize := by
    apply UScalar.eq_of_val_eq
    rw [R0Z.PoseidonRefine.uadd _ _ (by simp)]
    rfl
  rw [hr]
  simp only [core.slice.Slice.is_empty,core.slice.Slice.chunks,lift,bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ _ _ (by decide)]
  simp only [bind_tc_ok]
  rw [Array.index_mut_usize,index_ok _ 9#usize (by decide)]
  simp only [bind_tc_ok]
  have hp : input.length ≠ 0 := by simpa using hne
  simp only [hp,decide_false,Bool.false_eq_true,ite_false]
  simp only [BuilderForestStd.chunks,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,UScalar.ofNatCore_val_eq,
    Nat.reduceEqDiff,ite_false,bind_tc_ok]
  change (do
    let s ← poseidon2.hash_fields_with_trace_loop0 callback
      ⟨⟨input,8⟩,0#usize⟩ () (initial domain input)
    core.array.from_fn 8#usize
      (poseidon2.hash_fields_with_trace.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31 callback) s) = _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro s hs
  exact digest s
#print axioms shape

theorem success (domain : U32) (input : Slice U32) (d : Array U32 8#usize)
    (hd : domain.val < 2147483647) (hl : input.val.length < 2147483647)
    (hne : input.val ≠ []) (h : poseidon2.hash_fields domain input = ok d) :
    Canon8 d := by
  rw [shape domain input hne] at h
  pv_peel h with s hs
  cases h
  have hc := PV_L2C_HashLoopRange.success ⟨⟨input,8⟩,0#usize⟩
    (initial domain input) s (by change 0<8; omega) (initial_canonical domain input hd hl) hs
  intro j hj
  rw [digest8_get s j hj]
  exact hc ⟨j,by omega⟩
#print axioms success
end PV_L2C_HashRange
