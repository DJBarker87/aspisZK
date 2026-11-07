import NNG_SourceSplit087
import NNG_FilledReturned087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceFront087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 RSL.TX1_087.front LIB_Instances.VL a env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.tree (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env))) := by
 let s := NNG_PrepareInput087.input a obs env
 let head := invoke "TX1:064/filled" (14759#usize,0#u8) (NNG_Filled087.call env core.marker.CopyU8 14759#usize 0#u8)
 let k : core.result.Result (alloc.vec.Vec U8) aspis_core.r0.Error → Code (NNG_Front087.FrontOut Unit) := fun r=>
   match r with | .Err _=>pure (.Err verifier.Error.Allocation) | .Ok logical=>NNG_Front087.split (NNG_PrepareEmission087.calls env) s logical
 have split : NNG_Front087.tree (NNG_PrepareEmission087.calls env) s=NMT_CallTree.bind head k := by
   simp only [NNG_Front087.tree,NNG_PrepareEmission087.calls,head,k,Bind.bind]
   apply congrArg (NMT_CallTree.bind _)
   funext r
   cases r <;> rfl
 rw [split,←NNG_Canonical087.front_ref]
 have childLaw := NNG_Occurrences087.filled env 14759#usize (by decide)
 have headLaw := NNG_MapError087.law (fun _ : Unit=>LIB_Instances.VL.vAllocation) NNG_Filled087.port
   (NNG_Events087.events env) head env (LIB_Instances.VL.filled.run 14759) childLaw
 unfold NNG_Canonical087.front
 refine NNG_ResultBind137.sound head k
   (fun r=>NNG_MapError087.mapError (fun _ : Unit=>LIB_Instances.VL.vAllocation) (NNG_Filled087.port r))
   (NNG_FrontProjection087.port a env) (NNG_Events087.events env) env _ _ headLaw ?_
 intro reply returned
 have native := NNG_DLawStep136.invoke_returned (NNG_Events087.events env) "TX1:064/filled" _ _ _ returned
 cases reply with
 | Err e=>rfl
 | Ok logical=>
   exact NNG_SourceSplit087.source a obs env logical domain (NNG_FilledReturned087.length env 14759#usize logical native)
#print axioms source
end AspisR1.NNG_SourceFront087
