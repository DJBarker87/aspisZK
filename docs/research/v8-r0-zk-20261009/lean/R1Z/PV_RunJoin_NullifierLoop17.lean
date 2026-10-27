import R1Z.PV_RunJoin_NullifierControl17
import R1Z.PV_RunJoin_NullifierPermutation17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NullifierLoop17
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_RunJoin_NullifierData17 PV_RunJoin_NullifierControl17

def iter0 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32) :=
  ⟨⟨⟨key.val ++ salt.val,by rw [List.length_append,key.property,salt.property]; scalar_tac⟩,8⟩,0#usize⟩
def iter1 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32) :=
  ⟨⟨⟨salt.val,by rw [salt.property]; scalar_tac⟩,8⟩,1#usize⟩
def iter2 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32) :=
  ⟨⟨⟨[],by simp⟩,8⟩,2#usize⟩

theorem next0 : core.iter.adapters.enumerate.IteratorEnumerate.next
    (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice U32) iter0 =
    ok (some (0#usize,(⟨key.val,by rw [key.property]; scalar_tac⟩ : Slice U32)),iter1) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let n ← 0#usize + 1#usize
    ok (some (0#usize,(⟨key.val,by rw [key.property]; scalar_tac⟩ : Slice U32)),
      (⟨iter1.iter,n⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32)))) = _
  rw [PV_RunJoin_EnumerateTrace.checked_next _ (by simp)]
  have hn : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [uadd _ _ (by simp)]
    rfl
  rw [hn]
  rfl
#print axioms next0

theorem next1 : core.iter.adapters.enumerate.IteratorEnumerate.next
    (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice U32) iter1 =
    ok (some (1#usize,(⟨salt.val,by rw [salt.property]; scalar_tac⟩ : Slice U32)),iter2) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let n ← 1#usize + 1#usize
    ok (some (1#usize,(⟨salt.val,by rw [salt.property]; scalar_tac⟩ : Slice U32)),
      (⟨iter2.iter,n⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32)))) = _
  rw [PV_RunJoin_EnumerateTrace.checked_next _ (by simp)]
  have hn : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
    apply UScalar.eq_of_val_eq
    rw [uadd _ _ (by simp)]
    rfl
  rw [hn]
  rfl
#print axioms next1

theorem done : poseidon2.hash_fields_with_trace_loop0
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter2 () s5_23 = ok s5_23 := by
  rw [poseidon2.hash_fields_with_trace_loop0.eq_1 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter2 () s5_23]
  with_unfolding_all rfl
#print axioms done

theorem second : poseidon2.hash_fields_with_trace_loop0
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter1 () s4_23 = ok s5_23 := by
  rw [poseidon2.hash_fields_with_trace_loop0.eq_1 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter1 () s4_23,next1]
  change (do
    let state ← poseidon2.hash_fields_with_trace_loop0_loop0 saltIter s4_23
    let (out,c) ← poseidon2.permute_optimized_with_trace_threaded
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_RunJoin_HashCallback17.callback state ((),1#usize)
    poseidon2.hash_fields_with_trace_loop0
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter2 c.1 out) = ok s5_23
  rw [absorb_salt]
  simp only [bind_tc_ok,PV_RunJoin_NullifierPermutation17.second]
  exact done
#print axioms second

theorem first : poseidon2.hash_fields_with_trace_loop0
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter0 () initial = ok s5_23 := by
  rw [poseidon2.hash_fields_with_trace_loop0.eq_1 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter0 () initial,next0]
  change (do
    let state ← poseidon2.hash_fields_with_trace_loop0_loop0 keyIter initial
    let (out,c) ← poseidon2.permute_optimized_with_trace_threaded
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_RunJoin_HashCallback17.callback state ((),0#usize)
    poseidon2.hash_fields_with_trace_loop0
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter1 c.1 out) = ok s5_23
  rw [absorb_key]
  simp only [bind_tc_ok,PV_RunJoin_NullifierPermutation17.first]
  exact second
#print axioms first
end R1Z.PV_RunJoin_NullifierLoop17
