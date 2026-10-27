import FJl_SlotLiteral
import FJi_FourValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_FourLiteral
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical FIo_FieldBridge
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
def formula (gamma : E) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2) (s : Fin 4) : E :=
  (∑ l ∈ Finset.range 26,gamma^l*FJl_BaseLiteral.scalar c1 s l)+
    (gamma^28*LiteralOpeningView.eK (c1 s).2+
      gamma^26*LiteralOpeningView.eK (c2 s 0)+gamma^27*LiteralOpeningView.eK (c2 s 1))
/-- Complete four-slot source VALUE on the SAME opening's literal C1/C2 bytes. -/
theorem value (opening : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (gamma : E) (hg : FIo_ArrayCanon.Holds g)
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value g l.val=gamma^l.val)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((bytesOf opening.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (((bytesOf opening.val).drop 480).take 128)=some c2)
    (run : FIp_NativeDots.fast_dots.four_dots opening g=ok out) :
    ∀ s : Fin 4,FIp_ArrayValue.value out s.val=formula gamma c1 c2 s := by
  obtain ⟨selected,q,v0,v1,v2,v3,converted,hs,hc,hp,h0,h1,h2,h3,ho⟩ :=
    FIp_DotsReached.four opening g out run
  have shape := (FJi_PrefixValue.array selected q converted hc hp).trans
    (FJi_PrefixValue.selected opening selected hs)
  have bytes : bytesOf q.val=(bytesOf opening.val).take 608 := by
    rw [shape]
    exact List.map_take _ _ _
  have q1 : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c1 := by
    rw [bytes,List.take_take]
    exact d1
  have q2 : MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c2 := by
    rw [bytes,List.drop_take,List.take_take]
    exact d2
  subst out
  intro s
  fin_cases s
  · exact FJl_SlotLiteral.value q g gamma hg powers c1 c2 q1 q2 0 0#usize rfl v0 h0
  · exact FJl_SlotLiteral.value q g gamma hg powers c1 c2 q1 q2 1 1#usize rfl v1 h1
  · exact FJl_SlotLiteral.value q g gamma hg powers c1 c2 q1 q2 2 2#usize rfl v2 h2
  · exact FJl_SlotLiteral.value q g gamma hg powers c1 c2 q1 q2 3 3#usize rfl v3 h3
#print axioms value
end AspisR1.FJl_FourLiteral
end
