import ARX_TraceSupport
set_option autoImplicit false
namespace AspisR1.ARX_LogAgreement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- A complete recorded trace determines its cylinder even when it is supplied
by another observer, e.g. the bounded charge observer. -/
theorem consistent {X : Type} (p : Program Bytes State X) (K H : Bytes → State)
    (trace : List (Bytes × State)) (same : (eval K p).1 = trace)
    (replies : ∀ q ∈ trace, q.2 = H q.1) : ARS_AccountReplay.Consistent p K H := by
  intro address member
  obtain ⟨q,hq,eq⟩ := List.mem_map.mp member
  subst address
  exact (replies q (same ▸ hq)).symm.trans
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply K p q hq)
#print axioms consistent
end AspisR1.ARX_LogAgreement
