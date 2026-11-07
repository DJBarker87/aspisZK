import NNG_InvokeGraph094
import NNG_Candidate087
import NNG_PrepareTransport094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareGraph094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094
abbrev Observer := Option (verifier.Phase → Result Unit)
/-- The digest argument retained by the actual emitted call belongs to the
source trace as well as the child input. -/
theorem observation (a : NNG_PrepareInput087.Args) (env : RSL.Env) :
 NNG_Observed136.observation NNG_PrepareTransport094.port (NNG_Events094.events env)
  (invoke "TX1:087/prepare"
   (NNG_PrepareTransport094.digest env,fromT9 a.public_,NNG_Data137.bytes a.proof,(),(none : Observer),arr fromT3 a.g)
   (NNG_PrepareAdapter094.call env (NNG_PrepareTransport094.digest env) (fromT9 a.public_)
    (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)))=
 NNG_Producer087.producer a none env := by
 unfold NNG_Observed136.observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,NNG_Events094.prepare_call]
 rw [NNG_PrepareTransport094.call]
 unfold NNG_Events094.prepare
 rw [NNG_PrepareTransport094.input]
 unfold NNG_Producer087.producer
 generalize NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a none env)=r
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>
   apply congrArg (fun value=>RSL.Obs.mk (RSL.Exit.ret value) _)
   exact NNG_PrepareTransport094.output r
#print axioms observation

theorem occurrence (a : NNG_PrepareInput087.Args) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a none) :
 RSL.Spec.call (fun x : NNG_PrepareInput087.Args=>RSL.TX1_087.Domain LIB_Instances.VL x none)
  (RSL.TX1_087.Ref LIB_Instances.VL LIB_Instances.P) a env
  (NNG_Observed136.observation NNG_PrepareTransport094.port (NNG_Events094.events env)
   (invoke "TX1:087/prepare"
    (NNG_PrepareTransport094.digest env,fromT9 a.public_,NNG_Data137.bytes a.proof,(),(none : Observer),arr fromT3 a.g)
    (NNG_PrepareAdapter094.call env (NNG_PrepareTransport094.digest env) (fromT9 a.public_)
     (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)))) := by
 rw [observation]
 exact ⟨domain,NNG_Candidate087.candidate a none env domain⟩
#print axioms occurrence
end AspisR1.NNG_PrepareGraph094
