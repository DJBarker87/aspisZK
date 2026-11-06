import NLL_SamplerBound
import NHK_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL_QueryCarrier
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation

/-- Every successful CLOSED query invocation yields canonical physical words.
The SAME observed constructor supplies the returned array, including payloads;
there is no output equality supplied independently of the native cuts. -/
theorem source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv self row payload observed)
 (qs : Array U32 22#usize) (after : transcript.Transcript Unit)
 (returned : observed.result=ok (.Ok qs,after)) :
 ∀ j,j<22 → qs.val[j]!.val<262144 := by
 have all : ∀ w∈qs.val,w.val<262144 := by
   cases cuts with
   | absorbFail events error cut => cases returned
   | absorbDiv events cut => cases returned
   | pairsFail absorbed ae pe error ac pc => cases returned
   | pairsDiv absorbed ae pe ac pc => cases returned
   | returning absorbed ae pe blocks advances samplerOut ac pc sc =>
     have indices : ∀ i∈[0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize],i.val<8 := by
       intro i member
       simp only [List.mem_cons,List.not_mem_nil,or_false] at member
       rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> scalar_tac
     have good:=NLL_SamplerBound.native sc (NGQ_SamplerPacket.zip_bound blocks.val _ indices) NHB_Canonical.initial
     cases samplerOut with
     | Err error => cases returned
     | Ok pair =>
       rcases pair with ⟨queries,state⟩
       have same:=core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj returned))
       subst qs
       exact good
 intro j hj
 have length : qs.val.length=22 := qs.property
 have within : j<qs.val.length := by omega
 have canonical:=all qs.val[j] (List.getElem_mem within)
 simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem within,Option.getD_some] using canonical

set_option pp.proofs false
#print source
#print axioms source
end NLL_QueryCarrier
end
