import NFB_TailCount
import NFB_TailReadDomains
set_option autoImplicit false
noncomputable section
namespace NFB_TailAccepted
open Aeneas Aeneas.Std Result AspisR1 NFB_TailProgram

/-- Source-reachable tail packet. All three canonical input pairs, four count
values and same-receiver calls are derived from ONE accepted actual tail.
Native physical/callee assembly is still a separate OPEN obligation. -/
theorem complete (q : Array U8 608#usize) (g : Coeff) (slot : Usize) (out : E)
 (canonical : NEV_DotInputs.Canonical g)
 (accepted : NFA_SuffixFactor.tail q g slot=ok out) :
 ∃ (s0 s1 s2 s3 : Dot) (e0 e1 e2 : E) (q0 q1 q2 : Q),
 s0.count.val=0 ∧ s1.count.val=1 ∧ s2.count.val=2 ∧ s3.count.val=3 ∧
 NEV_DotCarrier.canonE e0 ∧ NEV_DotCarrier.canonQ q0 ∧
 NEV_DotCarrier.canonE e1 ∧ NEV_DotCarrier.canonQ q1 ∧
 NEV_DotCarrier.canonE e2 ∧ NEV_DotCarrier.canonQ q2 ∧
 FIo_Native.fast_pairing.EbyKDot.push s0 e0 q0=ok (.Ok (),s1) ∧
 FIo_Native.fast_pairing.EbyKDot.push s1 e1 q1=ok (.Ok (),s2) ∧
 FIo_Native.fast_pairing.EbyKDot.push s2 e2 q2=ok (.Ok (),s3) ∧
 FIo_Native.fast_pairing.EbyKDot.finish s3=ok out := by
 obtain ⟨s0,s1,s2,s3,e0,e1,e2,q0,q1,q2,stride,new,a0,p0,strideRun,a1,p1,a2,p2,finish⟩ :=
  NFB_TailCuts.complete q g slot out accepted
 obtain ⟨c0,c1,c2,c3⟩ := NFB_TailCount.chain s0 s1 s2 s3 e0 e1 e2 q0 q1 q2 new p0 p1 p2
 obtain ⟨ce0,cq0⟩ := NFB_TailReadDomains.first q g slot canonical e0 q0 a0
 obtain ⟨ce1,cq1⟩ := NFB_TailReadDomains.later q g stride 0#usize canonical (by decide) e1 q1 a1
 obtain ⟨ce2,cq2⟩ := NFB_TailReadDomains.later q g stride 1#usize canonical (by decide) e2 q2 a2
 exact ⟨s0,s1,s2,s3,e0,e1,e2,q0,q1,q2,c0,c1,c2,c3,ce0,cq0,ce1,cq1,ce2,cq2,p0,p1,p2,finish⟩
#print axioms complete
end NFB_TailAccepted
end
