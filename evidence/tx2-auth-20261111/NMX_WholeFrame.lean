import NMX_FrameLaws
set_option autoImplicit false
noncomputable section
namespace NMX_WholeFrame
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_Program
/-- Sequential full external-frame composition. No post-world is demanded on
stopped executions. This is model/source support, never a native packet. -/
theorem frame {W E A : Type} (handler : Handler W E)
 (steps : ∀ {B : Type} (cmd : Command B) before post reply events,
   handler cmd before = End.returned reply post events → post = before)
 (term : Program A) (before post : W)
 (reply : core.result.Result A PE) (events : List E)
 (run : eval handler term before = End.returned reply post events) : post = before := by
 induction term generalizing before post reply events with
 | ret a => cases run; rfl
 | reject e => cases run; rfl
 | stop cause => cases run
 | @step B cmd next ih =>
   cases h : handler cmd before with
   | stopped es cause => simp only [eval,h] at run; cases run
   | returned child mid es =>
     cases child with
     | Err e =>
       simp only [eval,h] at run
       have same := steps cmd before mid (.Err e) es h
       cases run
       exact same
     | Ok b =>
       have same := steps cmd before mid (.Ok b) es h
       cases value : eval handler (next b) mid with
       | stopped hs cause => simp only [eval,h,value,prepend] at run; cases run
       | returned result after hs =>
         simp only [eval,h,value,prepend] at run
         have complete := ih b mid after result hs value
         cases run
         exact complete.trans same
#print axioms frame
end NMX_WholeFrame
end
