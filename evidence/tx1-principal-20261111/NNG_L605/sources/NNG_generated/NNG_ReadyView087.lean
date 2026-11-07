import NNG_Ready137
import NNG_Slices087
import NNG_FrontValue087
import NNG_ObservedInput087
import NNG_ViewCanonical087
import LIBC_PreparedR4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReadyView087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Args:=NNG_PrepareInput087.Args

def Ready (sem : r1_semantic.Verified Unit) (v : verifier.View) : Prop :=
 NNG_VerifiedDomain136.Canonical (NNG_Output137.verified sem) ∧
 LIBC_PreparedDomain.Semantic (NMP_Transport.toT11 sem) ∧
 LIBC_PreparedDomain.Expanded (NNG_PrepareCarriers087.view v) ∧
 v.round0.val.length=224 ∧ v.round1.val.length=224 ∧ v.folded_root.isSome=true ∧
 v.final_message.val.length=2048 ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative (NNG_PrepareCarriers087.view v).inactive)

theorem observed (a : Args) (obs : RSL.Observer) (env : RSL.Env) (v : verifier.View)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : v.semantic.val.length≤57607)
 (out : r1_semantic.Verified Unit) (outv : verifier.View)
 (returned : NNG_FrontValue087.observed (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) v=
 .ok (.Ok (out,outv))) :
 v=outv ∧ NNG_VerifiedDomain136.Canonical (NNG_Output137.verified out) ∧
 LIBC_PreparedDomain.Semantic (NMP_Transport.toT11 out) := by
 unfold NNG_FrontValue087.observed at returned
 obtain ⟨reply,called,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ returned
 cases reply with
 | Err e=>cases tail
 | Ok sem=>
   have same:=core.result.Result.Ok.inj (Result.ok.inj tail)
   have eqSem:=congrArg Prod.fst same
   have eqView:=congrArg Prod.snd same
   subst out
   change NNG_Context137.emitted (NNG_Context137.calls env)
    ⟨NNG_PublicSource137.digest env,NMP_Transport.fromT9 a.public_,v.semantic,(),NNG_Context137.observer obs⟩=.ok (.Ok sem) at called
   rw [←NNG_ObservedInput087.input_exact a v obs env] at called
   have ready:=NNG_Ready137.returned (NNG_ObservedInput087.child a v) obs env
    (NNG_ObservedInput087.domain a v obs domain size) sem called
   exact ⟨eqView,ready⟩
#print axioms observed

theorem view (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 compact before : Slice U8)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (semSize : semantic.val.length=13831) (srcSize : compact.val.length=464) (dstSize : before.val.length=928)
 (checked : NFU_Retarget.compact.check_values compact=.ok (.Ok ()))
 (sameY1 : y1=LIBC_ExpandValuesModel.output compact before)
 (out : r1_semantic.Verified Unit) (outv : verifier.View)
 (returned : NNG_FrontValue087.view (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) semantic y1=
 .ok (.Ok (out,outv))) : Ready out outv := by
 unfold NNG_FrontValue087.view at returned
 obtain ⟨reply,called,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ returned
 cases reply with
 | Err e=>cases tail
 | Ok v=>
   have proofSize:=NNG_Slices087.proof_length a obs env domain
   have bound : 10055≤(NNG_PrepareInput087.input a obs env).bytes.val.length:=by rw [proofSize];decide
   have borrowed:=NNG_ViewShape087.borrowed _ semantic y1 bound v called
   have ready:=observed a obs env v domain (by rw [borrowed.1,semSize];decide) out outv tail
   subst outv
   have expanded:=LIBC_PreparedR4.expanded (NNG_PrepareCarriers087.view v) compact before srcSize dstSize checked
    (borrowed.2.trans sameY1)
   have dims:=NNG_ViewShape087.dimensions _ semantic y1 bound v called
   exact ⟨ready.2.1,ready.2.2,expanded,dims.1,dims.2.1,dims.2.2.1,dims.2.2.2,
    NNG_ViewCanonical087.returned _ semantic y1 bound v called⟩
#print axioms view
end AspisR1.NNG_ReadyView087
