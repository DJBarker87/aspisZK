import RPu_FJo_PrefixBytes
import RPu_FJl_SlotLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_FourLiteral
open Aeneas Aeneas.Std Result MultiproofConeCanonical FIo_FieldBridge
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
def formula (gamma : E) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2) (s : Fin 4) : E :=
  (∑ l ∈ Finset.range 26,gamma^l*FJl_BaseLiteral.scalar c1 s l)+
    (gamma^28*LiteralOpeningView.eK (c1 s).2+
      gamma^26*LiteralOpeningView.eK (c2 s 0)+gamma^27*LiteralOpeningView.eK (c2 s 1))
attribute [local irreducible] formula FIp_ArrayValue.value
theorem value (opening : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (gamma : E) (hg : FIo_ArrayCanon.Holds g)
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value g l.val=gamma^l.val)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((bytesOf opening.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (((bytesOf opening.val).drop 480).take 128)=some c2)
    (run : FIp_NativeDots.fast_dots.four_dots opening g=ok out) :
    ∀ s : Fin 4,FIp_ArrayValue.value out s.val=formula gamma c1 c2 s := by
  obtain ⟨selected,q,converted,hs,hc,hp,calls⟩ := FJo_FourCalls.reached opening g out run
  have bytes := FJo_PrefixBytes.value opening selected q converted hs hc hp
  have q1 : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c1 := by
    rw [bytes,List.take_take]; exact d1
  have q2 : MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c2 := by
    rw [bytes,List.drop_take,List.take_take]; exact d2
  intro s
  obtain ⟨v,call,read⟩ := calls s
  have h := FJl_SlotLiteral.value q g gamma hg powers c1 c2 q1 q2 s _ rfl v call
  unfold FIp_ArrayValue.value
  rw [read]
  simpa only [formula] using h
#print axioms value
end AspisR1.FJo_FourLiteral
end
