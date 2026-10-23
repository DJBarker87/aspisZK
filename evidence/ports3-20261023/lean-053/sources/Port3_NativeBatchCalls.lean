import Port3_NativeBatchBody

/-! Successful native batch calls retain all three roots and the same
scratch buffers in chronological order. This is not a Boolean/P6 erasure. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeBatchCalls
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeBatchBody
abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize

def rootAt (roots : Array (Array U8 32#usize) 3#usize) (i : Fin 3) : Array U8 32#usize :=
  roots.val[i.val]'(by simpa [roots.property] using i.isLt)

theorem root_read (roots : Array (Array U8 32#usize) 3#usize) (i : Fin 3) :
    Array.index_usize roots (Usize.ofNat i.val (by scalar_tac))=ok (rootAt roots i) := by
  simp [Array.index_usize,rootAt,List.getElem?_eq_getElem]

theorem values_calls (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize)
    (accepted : verifier.candidate.batch_merkle_values ops D proof queries roots batch hash=ok (.Ok ())) :
    ∃ (idx1 idx2 idx3 : Indices) (val1 val2 val3 : Values),
      verifier.candidate.batch_tree ops D proof queries (rootAt roots 0) batch 0#usize
        (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize (Array.repeat 32#usize 0#u8)) hash =
        ok (.Ok (),idx1,val1) ∧
      verifier.candidate.batch_tree ops D proof queries (rootAt roots 1) batch 1#usize idx1 val1 hash =
        ok (.Ok (),idx2,val2) ∧
      verifier.candidate.batch_tree ops D proof queries (rootAt roots 2) batch 2#usize idx2 val2 hash =
        ok (.Ok (),idx3,val3) := by
  have h0 : Array.index_usize roots 0#usize=ok (rootAt roots 0) := root_read roots 0
  have h1 : Array.index_usize roots 1#usize=ok (rootAt roots 1) := root_read roots 1
  have h2 : Array.index_usize roots 2#usize=ok (rootAt roots 2) := root_read roots 2
  unfold verifier.candidate.batch_merkle_values at accepted
  rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok] at accepted
  obtain ⟨⟨r0,idx1,val1⟩,call0,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
  cases r0 with
  | Err e => cases accepted
  | Ok unit =>
    cases unit
    dsimp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at accepted
    obtain ⟨⟨r1,idx2,val2⟩,call1,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    cases r1 with
    | Err e => cases accepted
    | Ok unit =>
      cases unit
      dsimp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at accepted
      obtain ⟨⟨r2,idx3,val3⟩,call2,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
      cases r2 with
      | Err e => cases accepted
      | Ok unit =>
        cases unit
        exact ⟨idx1,idx2,idx3,val1,val2,val3,call0,call1,call2⟩

#print axioms root_read
#print axioms values_calls
end AspisR1.Port3_NativeBatchCalls
end
