import RPu_FJl_M31ArrayValue
import RPu_FJl_SliceCopy
import RPu_FJl_C1Coordinates
import RPu_FJl_WindowArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ScalarLiteral
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical ExactLeafFieldCodec MixedLeafEncoding
/-- Actual native scalar VALUE equals its SAME strict C1 literal coordinate. -/
theorem value (q : Array U8 608#usize) (c : MixedLeafEncoding.C1)
    (decoded : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c)
    (s : Fin 4) (l : Fin 26) (slot term : Usize)
    (hs : slot.val=s.val) (hl : term.val=l.val) (x : U32)
    (run : JFr_TX2_ScalarRead.read q slot term=ok x) :
    (x.val : M31Exact)=(c s).1 l := by
  obtain ⟨a,hbytes,hdecode⟩ := FJl_SliceCopy.scalar q slot term x run
  have native := FJl_M31ArrayValue.value a x hdecode
  have literal := FJl_C1Coordinates.scalar ((bytesOf q.val).take 480) c decoded s l
  rw [FJl_WindowArithmetic.scalar _ _ _ s.isLt l.isLt] at literal
  have bytes : bytesOf a.val=((bytesOf q.val).drop (120*s.val+4*l.val)).take 4 := by
    rw [hbytes]
    simp only [bytesOf,List.map_take,List.map_drop,hs,hl,Nat.mul_comm]
  rw [bytes,literal] at native
  exact (Option.some.inj native).symm
#print axioms value
end AspisR1.FJl_ScalarLiteral
end
