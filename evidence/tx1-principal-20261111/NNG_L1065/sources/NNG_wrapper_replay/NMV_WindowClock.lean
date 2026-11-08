import NMV_WindowEval
set_option autoImplicit false
namespace NMV_WindowClock
open RSL NMV_WindowEval

/-- The runtime window is exact, including its event, for both clock replies. -/
theorem exact_clock (w : Windows) (env : Env) :
 w.clock env = ⟨.ret env.clock,[.clock env.clock]⟩ := by
 have h := w.clock_law env
 rcases h with ⟨c,e1,o2,hc,h2,ho⟩ | ⟨e1,hc,ho⟩ | ⟨e1,hc,ho⟩
 · simp only [Spec.env,Obs.mk.injEq,Exit.ret.injEq] at hc
   rcases hc with ⟨rfl,rfl⟩
   rcases h2 with ⟨u,e2,o3,hu,h3,h2⟩ | ⟨e2,hu,h2⟩ | ⟨e2,hu,h2⟩
   · simp only [Spec.emit,Obs.mk.injEq,Exit.ret.injEq] at hu
     rcases hu with ⟨_,rfl⟩
     simp only [Spec.pure] at h3
     subst h3
     subst h2
     simpa using ho
   · simp [Spec.emit] at hu
   · simp [Spec.emit] at hu
 · simp [Spec.env] at hc
 · simp [Spec.env] at hc

#print axioms exact_clock
end NMV_WindowClock
