import NCM_PaddingPredicate

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_PaddingScan
open Aeneas Aeneas.Std Result NCE_PaddingCuts

def allZero (chunks : List (Slice U8)) : Bool := chunks.all (fun c => c.val.all (fun b => b == 0#u8))

/-- Totality and exact stop Boolean for the installed predicate. The returned
iterator is the actual first-stop suffix; it is not forced empty. -/
theorem value (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (chunks : List (Slice U8)) (remainder : Slice U8)
    (sizes : ∀ c ∈ chunks, c.val.length = 8) :
    ∃ after, NBI_Padding.scan (NCM_PaddingPredicate.predicate base D) remainder chunks = ok (!allZero chunks,after) := by
  induction chunks with
  | nil => exact ⟨{chunks:=[],remainder:=remainder},rfl⟩
  | cons chunk rest ih =>
    have size := sizes chunk (by simp)
    have call := NCM_PaddingPredicate.observation base D chunk size
    change Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut
      (Port3_BatchStd.install base) D () chunk = _ at call
    obtain ⟨after,tail⟩ := ih (fun c mem => sizes c (List.mem_cons_of_mem _ mem))
    cases zero : chunk.val.all (fun b => b == 0#u8) with
    | false =>
      refine ⟨{chunks:=rest,remainder:=remainder},?_⟩
      simp only [NBI_Padding.scan,call,zero,
        Bool.not_false,bind_tc_ok,if_true,allZero,List.all_cons,Bool.false_and]
      rfl
    | true =>
      refine ⟨after,?_⟩
      simp only [NBI_Padding.scan,call,zero,
        Bool.not_true,bind_tc_ok,Bool.false_eq_true,if_false,tail,allZero,List.all_cons,Bool.true_and]
      rfl

/-- Native one-iteration padding cuts consume the SAME partition and caller
frame. This is a derived total loop result, not a native premise. -/
theorem native_value {Frame : Type} (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (native : Body Frame)
    (cut : NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) native)
    (chunks : List (Slice U8)) (remainder : Slice U8) (frame : Frame)
    (sizes : ∀ c ∈ chunks, c.val.length = 8) :
    ∃ after, run native (chunks.length+1) ({chunks:=chunks,remainder:=remainder},frame) =
      ok (!allZero chunks,after,frame) := by
  obtain ⟨after,returned⟩ := value base D chunks remainder sizes
  refine ⟨after,?_⟩
  rw [run_eq _ native cut chunks remainder frame sizes,returned]
  rfl

#print axioms value
#print axioms native_value
end AspisR1.NCM_PaddingScan
end
