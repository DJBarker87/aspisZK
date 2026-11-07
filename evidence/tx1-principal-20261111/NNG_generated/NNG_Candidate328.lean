import NNG_Child328
import NNG_Tail328
import NNG_Producer328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate328
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_Carriers328

/-- Full first_decoded at the concrete094 child, original caller domain,
complete Result arms, and exact error log after the child's event prefix. -/
theorem candidate : RSL.TX1_328.RowSpec_328 LIB_Instances.VL LIB_Instances.P NNG_Producer328.producer := by
 intro a env own
 rw [NNG_Producer328.tree]
 have domain : RSL.TX1_094.Domain LIB_Instances.VL a none a.public_ := ⟨rfl,own⟩
 have child : RSL.Spec.call (fun x : NNG_Input094.Args=>RSL.TX1_094.Domain LIB_Instances.VL x none x.public_)
  (RSL.TX1_094.Ref LIB_Instances.VL LIB_Instances.P) a env
  (observation childPort (NNG_Tree328.events env) (NNG_Tree328.child (NNG_Native328.input a) env)) :=
  Eq.mp (congrArg (fun o=>RSL.Spec.call
   (fun x : NNG_Input094.Args=>RSL.TX1_094.Domain LIB_Instances.VL x none x.public_)
   (RSL.TX1_094.Ref LIB_Instances.VL LIB_Instances.P) a env o) (NNG_Child328.original a env domain).symm)
   ⟨domain,NNG_Candidate094.candidate a none env domain⟩
 unfold RSL.TX1_328.Ref NNG_Tree328.tree
 apply NNG_SourceStep136.bind_sound _ _ childPort port (NNG_Tree328.events env) env _ _ child
 intro r returned
 exact NNG_Tail328.source env r
#check candidate
#print axioms candidate
end AspisR1.NNG_Candidate328
