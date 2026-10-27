import RPu_FJi_SlotValue
import RPu_FJl_SlotReads
import RPu_FJl_BaseLiteral
import RPu_FJl_TailLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_SlotLiteral
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open MultiproofConeCanonical FIo_FieldBridge
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
/-- Complete backend VALUE on the SAME29 coefficients and literal C1/C2 bytes.
All arithmetic VALUE lemmas are imported from FJi; only operand transport is new. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (gamma : E)
    (hg : FIo_ArrayCanon.Holds g) (powers : ∀ l : Fin 29,FIp_ArrayValue.value g l.val=gamma^l.val)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c2)
    (s : Fin 4) (slot : Usize) (hs : slot.val=s.val) (out : NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    decodeWide (wide out)=
      (∑ l ∈ Finset.range 26,gamma^l*FJl_BaseLiteral.scalar c1 s l)+
      (gamma^28*LiteralOpeningView.eK (c1 s).2+
        gamma^26*LiteralOpeningView.eK (c2 s 0)+gamma^27*LiteralOpeningView.eK (c2 s 1)) := by
  have native := FJi_SlotValue.value q g slot out hg run
  obtain ⟨reads,q0,q1,q2,r0,r1,r2⟩ := FJl_SlotReads.reached q g slot out run
  have t0 : FJf_EbyKCodec.scalar q0=LiteralOpeningView.eK (c1 s).2 := by
    unfold FJf_EbyKCodec.scalar
    rw [FJl_TailLiteral.c1 q c1 d1 s slot hs q0 r0]
    rfl
  have t1 : FJf_EbyKCodec.scalar q1=LiteralOpeningView.eK (c2 s 0) := by
    unfold FJf_EbyKCodec.scalar
    rw [FJl_TailLiteral.c2first q c2 d2 s slot hs q1 r1]
    rfl
  have t2 : FJf_EbyKCodec.scalar q2=LiteralOpeningView.eK (c2 s 1) := by
    unfold FJf_EbyKCodec.scalar
    rw [FJl_TailLiteral.c2second q c2 d2 s slot hs q2 r2]
    rfl
  rw [native.2,FJi_SlotValue.model,FJi_TailTrace.model,
    FJl_BaseLiteral.value q g gamma powers c1 d1 s slot hs reads 26 (by decide),
    FJi_TailInputs.observed_value _ q0 r0,FJi_TailInputs.observed_value _ q1 r1,
    FJi_TailInputs.observed_value _ q2 r2,t0,t1,t2,
    powers ⟨28,by decide⟩,powers ⟨26,by decide⟩,powers ⟨27,by decide⟩]
#print axioms value
end AspisR1.FJl_SlotLiteral
end
