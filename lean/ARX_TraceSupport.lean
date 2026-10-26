import ARU_Factory
import ARW_AdmittedSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_TraceSupport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem consistent {X : Type} (p : Program Bytes State X) (H K : Bytes → State)
    (same : (eval H p).1 = (eval K p).1) : ARS_AccountReplay.Consistent p H K := by
  intro address member
  obtain ⟨q,hq,eq⟩ := List.mem_map.mp member
  subst address
  have a := Op5I_AcceptedCarrierCounterexample.evaluated_reply H p q hq
  have b := Op5I_AcceptedCarrierCounterexample.evaluated_reply K p q (same ▸ hq)
  exact b.symm.trans a

#print axioms consistent
end AspisR1.ARX_TraceSupport
end
