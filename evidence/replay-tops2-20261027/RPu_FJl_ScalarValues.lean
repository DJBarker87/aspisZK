import RPu_FJl_ScalarLiteral
import RPu_FJl_InnerReads
import RPu_FJi_WidePack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ScalarValues
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical
/-- Identify every source scalar observation with its SAME literal C1 coordinate. -/
theorem value (q : Array U8 608#usize) (c : MixedLeafEncoding.C1)
    (decoded : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c)
    (s : Fin 4) (slot : Usize) (hs : slot.val=s.val)
    (reads : ∀ n,n<26 → FJl_InnerReads.Read q slot n) (l : Fin 26) :
    FJi_WidePack.base (FJi_Inputs.scalar q slot (FJi_Inputs.cursor l.val)).val=
      ExactBaseProjection.embed ((c s).1 l) := by
  obtain ⟨term,x,hn,run⟩ := reads l.val l.isLt
  have cursor : FJi_Inputs.cursor l.val=term := by
    rw [←hn]
    exact FJi_Inputs.cursor_same term (by rw [hn];exact l.isLt)
  rw [cursor,FJi_Inputs.scalar_value q slot term x run]
  have h := FJl_ScalarLiteral.value q c decoded s l slot term hs hn x run
  have embedding (x : ExactLeafFieldCodec.M31Exact) :
      FJi_WidePack.base x=ExactBaseProjection.embed x := rfl
  rw [embedding,h]
#print axioms value
end AspisR1.FJl_ScalarValues
end
