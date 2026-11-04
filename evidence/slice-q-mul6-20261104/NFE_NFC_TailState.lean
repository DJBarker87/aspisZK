import NFE_NFC_TailTrace
import NFE_NEI_PublicDotFinishValues
import NFC_ArrayFour
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_TailState
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailTrace

theorem new_count (state : Acc) (run : FIo_Native.fast_pairing.EbyKDot.new=ok state) :
    state.count.val=0 := by
  unfold FIo_Native.fast_pairing.EbyKDot.new FIo_Native.fast_pairing.canonical.Dot.new at run
  simp only [bind_tc_ok] at run
  cases run
  rfl

theorem finish_canonical (state : Acc) (out : NE)
    (run : FIo_Native.fast_pairing.EbyKDot.finish state=ok out) : canonE out := by
  rcases state with ⟨⟨left⟩,⟨right⟩,count⟩
  obtain ⟨a,b,c,d,hl⟩:=NFC_ArrayFour.shape left
  obtain ⟨e,f,g,h,hr⟩:=NFC_ArrayFour.shape right
  subst left
  subst right
  obtain ⟨actual,call,h0,h1,h2,h3,h4,h5,h6,h7⟩:=NFE_NEI_PublicDotFinishValues.source a b c d e f g h count
  have same : actual=out := Result.ok.inj (call.symm.trans run)
  subst actual
  unfold canonE canonQ canonC
  exact ⟨⟨⟨by rw [h0];omega,by rw [h1];omega⟩,⟨by rw [h2];omega,by rw [h3];omega⟩⟩,
    ⟨⟨by rw [h4];omega,by rw [h5];omega⟩,⟨by rw [h6];omega,by rw [h7];omega⟩⟩⟩

/-- Every count guard is derived on the actual receiver chain. -/
theorem chain (s0 s1 s2 s3 : Acc) (w0 w1 w2 : NE) (x0 x1 x2 : NQ)
    (new : FIo_Native.fast_pairing.EbyKDot.new=ok s0)
    (p0 : FIo_Native.fast_pairing.EbyKDot.push s0 w0 x0=ok (.Ok (),s1))
    (p1 : FIo_Native.fast_pairing.EbyKDot.push s1 w1 x1=ok (.Ok (),s2))
    (p2 : FIo_Native.fast_pairing.EbyKDot.push s2 w2 x2=ok (.Ok (),s3)) :
    s0.count.val=0 ∧ s1.count.val=1 ∧ s2.count.val=2 ∧ s3.count.val=3 := by
  have c0:=new_count s0 new
  have c1:=NFA_TailCounter.step s0 w0 x0 s1 (by omega) p0
  have c2:=NFA_TailCounter.step s1 w1 x1 s2 (by omega) p1
  have c3:=NFA_TailCounter.step s2 w2 x2 s3 (by omega) p2
  exact ⟨c0,by omega,by omega,by omega⟩

theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (out : NE) (canonical : NEV_DotInputs.Canonical g)
    (run : NFE_NFA_SuffixFactor.tail q g slot=ok out) : canonE out ∧
    ∃ (s0 s1 s2 s3 : Acc) (w0 w1 w2 : NE) (x0 x1 x2 : NQ),
      s0.count.val=0 ∧ s1.count.val=1 ∧ s2.count.val=2 ∧ s3.count.val=3 ∧
      canonE w0 ∧ canonE w1 ∧ canonE w2 ∧ canonQ x0 ∧ canonQ x1 ∧ canonQ x2 ∧
      FIo_Native.fast_pairing.EbyKDot.push s0 w0 x0=ok (.Ok (),s1) ∧
      FIo_Native.fast_pairing.EbyKDot.push s1 w1 x1=ok (.Ok (),s2) ∧
      FIo_Native.fast_pairing.EbyKDot.push s2 w2 x2=ok (.Ok (),s3) ∧
      FIo_Native.fast_pairing.EbyKDot.finish s3=ok out := by
  obtain ⟨s0,s1,s2,s3,w0,w1,w2,x0,x1,x2,new,_,_,_,cw0,cw1,cw2,cx0,cx1,cx2,p0,p1,p2,finish⟩:=
    NFE_NFC_TailTrace.accepted q g slot out canonical run
  obtain ⟨c0,c1,c2,c3⟩:=chain s0 s1 s2 s3 w0 w1 w2 x0 x1 x2 new p0 p1 p2
  exact ⟨finish_canonical s3 out finish,s0,s1,s2,s3,w0,w1,w2,x0,x1,x2,
    c0,c1,c2,c3,cw0,cw1,cw2,cx0,cx1,cx2,p0,p1,p2,finish⟩
#print axioms new_count
#print axioms finish_canonical
#print axioms chain
#print axioms accepted
end AspisR1.NFE_NFC_TailState
end
