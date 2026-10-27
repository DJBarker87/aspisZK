import RPv_FJh_InternalWeights
import RPv_FJh_InternalConstantIndices
import RPv_FJh_InternalConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalConstantCalls
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (cell)
open FJh_InternalWeights (index rows)
abbrev even := state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
abbrev odd := state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
theorem even_call (i : Fin 7) : even.call_mut () (index i)=
    ok (FJh_InternalConstants.value ⟨2*i.val,by omega⟩,()) := by
  obtain ⟨offset,e,o,rs,rm,ve,ra,vo⟩ := FJh_InternalConstantIndices.value i
  have he : e.val<14 := by omega
  have read := FJh_InternalConstants.read e he
  simp only [even,
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31,
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut,
    rs,rm,read,bind_tc_ok]
  exact congrArg (fun j : Fin 14=>ok (FJh_InternalConstants.value j,())) (Fin.ext ve)

theorem odd_call (i : Fin 7) : odd.call_mut () (index i)=
    ok (FJh_InternalConstants.value ⟨2*i.val+1,by omega⟩,()) := by
  obtain ⟨offset,e,o,rs,rm,ve,ra,vo⟩ := FJh_InternalConstantIndices.value i
  have ho : o.val<14 := by omega
  have read := FJh_InternalConstants.read o ho
  simp only [odd,
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31,
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut,
    rs,rm,ra,read,bind_tc_ok]
  exact congrArg (fun j : Fin 14=>ok (FJh_InternalConstants.value j,())) (Fin.ext vo)

theorem cells (f : core.ops.function.FnMut Unit Usize U32) (out : Array U32 7#usize)
    (run : FIq_Native.core.array.Array.map f rows ()=ok out) (i : Fin 7) :
    f.call_mut () (index i)=ok (cell out i,()) := by
  unfold FIq_Native.core.array.Array.map at run
  have rel := FJa_MapRelation.value f (fun j v=>f.call_mut () j=ok (v,())) rows () out
    (by intro j hj v last called;cases last;exact ⟨called,rfl⟩) run
  exact FJh_MapCells.get rel i.val (by rw [rows.property];exact i.isLt)
    (by rw [out.property];exact i.isLt)
theorem even_value (out : Array U32 7#usize)
    (run : FIq_Native.core.array.Array.map even rows ()=ok out) (i : Fin 7) :
    cell out i=FJh_InternalConstants.value ⟨2*i.val,by omega⟩ := by
  exact congrArg Prod.fst (Result.ok.inj ((cells even out run i).symm.trans (even_call i)))
theorem odd_value (out : Array U32 7#usize)
    (run : FIq_Native.core.array.Array.map odd rows ()=ok out) (i : Fin 7) :
    cell out i=FJh_InternalConstants.value ⟨2*i.val+1,by omega⟩ := by
  exact congrArg Prod.fst (Result.ok.inj ((cells odd out run i).symm.trans (odd_call i)))
#print axioms even_call
#print axioms odd_call
#print axioms cells
#print axioms even_value
#print axioms odd_value
end AspisR1.FJh_InternalConstantCalls
end
