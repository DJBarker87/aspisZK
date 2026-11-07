import NNG_SourceObserved087
import NNG_ViewShape087
import NNG_Occurrences087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceView087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (proofSize : (NNG_PrepareInput087.input a obs env).bytes.val.length=57607)
 (semSize : semantic.val.length=13831) (y1Size : y1.val.length=928) :
 NNG_Canonical087.view LIB_Instances.VL a (LIB_Carriers.bytes semantic) (LIB_Carriers.bytes y1) env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.view (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) semantic y1)) := by
 let s := NNG_PrepareInput087.input a obs env
 let head := invoke "TX1:095/wide_view" (s.bytes,semantic,y1) (NNG_WideView087.call s.bytes semantic y1)
 let k : core.result.Result verifier.View verifier.Error → Code (NNG_Front087.FrontOut Unit) := fun r=>
   match r with | .Err e=>pure (.Err e) | .Ok v=>NNG_Front087.observed (NNG_PrepareEmission087.calls env) s v
 have split : NNG_Front087.view (NNG_PrepareEmission087.calls env) s semantic y1=NMT_CallTree.bind head k := by
   simp only [NNG_Front087.view,head,k,Bind.bind,NNG_PrepareEmission087.calls]
   apply congrArg (NMT_CallTree.bind _)
   funext reply
   cases reply <;> rfl
 rw [split]
 have childDomain : LIBC_WideView.Domain (LIB_Carriers.bytes s.bytes,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) := by
   change _ ∧ _ ∧ _
   simpa only [NMS_R2N_RSLScalars.bytes_length] using And.intro proofSize (And.intro semSize y1Size)
 have rawLaw := NNG_Occurrences087.view env s.bytes semantic y1 childDomain
 have argEq : (LIB_Carriers.bytes s.bytes,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1)=
   (a.proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) :=
   congrArg (fun proof=>(proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1)) (NNG_PrepareInput087.proof_exact a obs env domain)
 have headLaw := Eq.mp (congrArg (fun args=>LIBC_WideView.child.run args env
   (observation NNG_WideView087.port (NNG_Events087.events env) head)) argEq) rawLaw
 unfold NNG_Canonical087.view
 refine NNG_ResultBind137.sound head k NNG_WideView087.port (NNG_FrontProjection087.port a env)
   (NNG_Events087.events env) env _ _ headLaw ?_
 intro reply returned
 have native := NNG_DLawStep136.invoke_returned (NNG_Events087.events env) "TX1:095/wide_view" _ _ _ returned
 cases reply with
 | Err e=>rfl
 | Ok v=>
   have borrowed := NNG_ViewShape087.borrowed s.bytes semantic y1 (by change 10055≤_;rw [proofSize];decide) v native
   exact NNG_SourceObserved087.source a obs env v domain (by rw [borrowed.1,semSize];decide)
#print axioms source
end AspisR1.NNG_SourceView087
