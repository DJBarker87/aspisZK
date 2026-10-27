import RPt_FJl_M31ArrayValue
import RPt_FJl_SliceCopy
import RPt_FJl_InnerReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ScalarDecode
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- An actual scalar read supplies a strict decoder witness at its source offset. -/
theorem value (q : Array U8 608#usize) (slot : Usize)
    (reads : ∀ n,n<26 → FJl_InnerReads.Read q slot n) (l : Fin 26) :
    ∃ x,ExactLeafFieldCodec.decodeM31
      (OraclePortCompactDraft.slice (bytesOf q.val) (120*slot.val+4*l.val) 4)=some x := by
  obtain ⟨term,x,ht,call⟩ := reads l.val l.isLt
  obtain ⟨a,bytes,decode⟩ := FJl_SliceCopy.scalar q slot term x call
  refine ⟨(x.val : ExactLeafFieldCodec.M31Exact),?_⟩
  have strict := FJl_M31ArrayValue.value a x decode
  rw [bytes] at strict
  simpa only [bytesOf,List.map_take,List.map_drop,ht,OraclePortCompactDraft.slice,Nat.mul_comm] using strict
#print axioms value
end AspisR1.FJo_ScalarDecode
end
