import NBQ_PublicInvariant
set_option autoImplicit false
namespace NBQ_TailDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- Three real tail invocations on one state chain. The count domain for each
callee is derived from the preceding source result, never supplied. -/
theorem three (a28 a26 a27 : NE) (q0 q1 q2 : NQ)
    (h28 : canonE a28) (h26 : canonE a26) (h27 : canonE a27)
    (hq0 : canonQ q0) (hq1 : canonQ q1) (hq2 : canonQ q2) :
    ∃ s0 s1 s2 s3 out,
      FIo_Native.fast_pairing.EbyKDot.new=ok s0 ∧
      FIo_Native.fast_pairing.EbyKDot.push s0 a28 q0=ok (.Ok (),s1) ∧
      FIo_Native.fast_pairing.EbyKDot.push s1 a26 q1=ok (.Ok (),s2) ∧
      FIo_Native.fast_pairing.EbyKDot.push s2 a27 q2=ok (.Ok (),s3) ∧
      s0.count.val=0 ∧ s1.count.val=1 ∧ s2.count.val=2 ∧ s3.count.val=3 ∧
      NBQ_PublicInvariant.Inv s3 ∧
      FIo_Native.fast_pairing.EbyKDot.finish s3=ok out ∧ canonE out := by
  obtain ⟨s0,new,h0⟩ := NBQ_PublicInvariant.initial
  have z : s0.count.val=0 := by
    have eq := Result.ok.inj (new.symm.trans NBQ_U06.new)
    rw [eq];rfl
  obtain ⟨s1,r1,h1,c1⟩ := NBQ_PublicInvariant.step s0 a28 q0 h0 (by omega) h28 hq0
  obtain ⟨s2,r2,h2,c2⟩ := NBQ_PublicInvariant.step s1 a26 q1 h1 (by omega) h26 hq1
  obtain ⟨s3,r3,h3,c3⟩ := NBQ_PublicInvariant.step s2 a27 q2 h2 (by omega) h27 hq2
  obtain ⟨out,finished,canonical⟩ := NBQ_U06.finish s3
  exact ⟨s0,s1,s2,s3,out,new,r1,r2,r3,z,by omega,by omega,by omega,h3,finished,canonical⟩
#print axioms three
end NBQ_TailDomain
