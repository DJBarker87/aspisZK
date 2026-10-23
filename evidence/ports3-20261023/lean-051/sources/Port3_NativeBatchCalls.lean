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
  have h0 := root_read roots 0
  have h1 := root_read roots 1
  have h2 := root_read roots 2
  unfold verifier.candidate.batch_merkle_values at accepted
  simp only [show Usize.ofNat (0 : Fin 3).val (by scalar_tac)=0#usize by rfl,
    show Usize.ofNat (1 : Fin 3).val (by scalar_tac)=1#usize by rfl,
    show Usize.ofNat (2 : Fin 3).val (by scalar_tac)=2#usize by rfl,h0,h1,h2,bind_tc_ok] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    refine ⟨_,_,_,_,_,_,?_,?_,?_⟩ <;> assumption

#print axioms root_read
#print axioms values_calls
end AspisR1.Port3_NativeBatchCalls
end
