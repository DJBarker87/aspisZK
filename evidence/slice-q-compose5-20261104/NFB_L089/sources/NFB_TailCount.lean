import NFB_TailDefs
set_option autoImplicit false
noncomputable section
namespace NFB_TailCount
open Aeneas Aeneas.Std Result AspisR1 NFB_TailProgram

theorem initial (self : Dot) (run : FIo_Native.fast_pairing.EbyKDot.new=ok self) :
 self.count.val=0 := by
 unfold FIo_Native.fast_pairing.EbyKDot.new at run
 obtain ⟨d,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases Result.ok.inj run
 rfl

/-- All four receiver counts follow from actual reached pushes, rather than
being independently assumed for a native loop pre-state. -/
theorem chain (s0 s1 s2 s3 : Dot) (e0 e1 e2 : E) (q0 q1 q2 : Q)
 (new : FIo_Native.fast_pairing.EbyKDot.new=ok s0)
 (p0 : FIo_Native.fast_pairing.EbyKDot.push s0 e0 q0=ok (.Ok (),s1))
 (p1 : FIo_Native.fast_pairing.EbyKDot.push s1 e1 q1=ok (.Ok (),s2))
 (p2 : FIo_Native.fast_pairing.EbyKDot.push s2 e2 q2=ok (.Ok (),s3)) :
 s0.count.val=0 ∧ s1.count.val=1 ∧ s2.count.val=2 ∧ s3.count.val=3 := by
 have c0:=initial s0 new
 have c1:=NFA_TailCounter.step s0 e0 q0 s1 (by omega) p0
 have c2:=NFA_TailCounter.step s1 e1 q1 s2 (by omega) p1
 have c3:=NFA_TailCounter.step s2 e2 q2 s3 (by omega) p2
 omega
#print axioms initial
#print axioms chain
end NFB_TailCount
end
