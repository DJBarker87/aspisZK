import NNG_PreparedOccurrence087
import NNG_ReadyFront087
import NNG_FrontErase087
import NNG_SourceFront087
import NNG_Factor087
import NNG_Producer087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136

theorem candidate : RSL.TX1_087.RowSpec_087 LIB_Instances.VL LIB_Instances.P NNG_Producer087.producer := by
 intro a obs env domain
 rw [NNG_Producer087.tree,←NNG_Factor087.tree]
 unfold RSL.TX1_087.Ref
 refine NNG_SourceStep136.bind_sound
  (NNG_Front087.tree (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env))
  (NNG_Factor087.finish (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env))
  (NNG_FrontProjection087.port a env) NNG_PreparedCall087.port (NNG_Events087.events env) env _ _
  (NNG_SourceFront087.source a obs env domain) ?_
 intro reply returned
 cases reply with
 | Err e=>
  change RSL.Spec.pure (.error (NNG_PrepareErrors087.error e),a.g) env
   (observation NNG_PreparedCall087.port (NNG_Events087.events env)
    (pure (.Err e,(NNG_PrepareInput087.input a obs env).scratch)))
  change RSL.Obs.mk (RSL.Exit.ret (.error (NNG_PrepareErrors087.error e),
   NMT_Transport.arr NNG_PrepareCarriers087.wide (NNG_PrepareInput087.input a obs env).scratch)) []=
    RSL.Obs.mk (RSL.Exit.ret (.error (NNG_PrepareErrors087.error e),a.g)) []
  exact congrArg (fun g=>RSL.Obs.mk (RSL.Exit.ret (.error (NNG_PrepareErrors087.error e),g)) [])
    (NNG_PrepareInput087.scratch_exact a obs env)
 | Ok pair=>
  rcases pair with ⟨sem,v⟩
  have native:=NNG_SourceStep136.returned_run (NNG_Events087.events env) _ _ returned
  rw [run_result,NNG_FrontErase087.tree] at native
  have ready:=NNG_ReadyFront087.returned a obs env domain sem v native
  change LIB_Prepared.child.run (NNG_FrontProjection087.verified a env v sem,NNG_PrepareCarriers087.view v,a.g) env
   (observation NNG_PreparedCall087.port (NNG_Events087.events env)
    (NNG_Tree087.mark (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) v sem))
  unfold NNG_Tree087.mark
  simp only [NNG_PrepareEmission087.calls,Bind.bind]
  rw [NNG_Head087.invoke_ok _ env _ _ _ _ (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
  exact NNG_PreparedOccurrence087.occurrence a obs env sem v ready
#print axioms candidate
end AspisR1.NNG_Candidate087
