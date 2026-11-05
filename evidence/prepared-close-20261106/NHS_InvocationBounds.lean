import NHS_QueryBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_InvocationBounds
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The actual returning query observation has22 bounded indices; the bounds
are conclusions of its own chronological cuts. -/
theorem source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv self row payload observed)
 (q : Array U32 22#usize) (after : transcript.Transcript Unit)
 (returned : observed.result=ok (.Ok q,after)) : ∀ w∈q.val,w.val<262144 := by
 cases cuts with
 | absorbFail => cases returned
 | absorbDiv => cases returned
 | pairsFail => cases returned
 | pairsDiv => cases returned
 | returning absorbed absorbEvents pairEvents blocks advances out absorbCut pairCuts samplerCuts =>
   have bounds := NHS_QueryBounds.blocks samplerCuts NHB_Canonical.initial
   cases out with
   | Err e => cases returned
   | Ok pair =>
     have equal := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj returned))
     cases equal
     exact bounds
#print axioms source
end AspisR1.NHS_InvocationBounds
