import NLL_QueryCarrier
import NFW_PreparedCalls
import NFW_PreparedPort
set_option autoImplicit false
noncomputable section
namespace NLL_Tx1QueryCarrier
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation

/-- The literal Prepared::new output constructor used by CLOSED TX1:179
carries THAT query array unchanged into the batch helper's nominal port.
The enclosing native prepare/tx1 invocation must install its returned
constructor; no independent p or query-array equality is assumed here. -/
theorem source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv self row payload observed)
 (qs : Array U32 22#usize) (after : transcript.Transcript Unit)
 (returned : observed.result=ok (.Ok qs,after))
 (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (gamma kappa claim : aspis_core.field.WideExact) (alpha : Array aspis_core.field.WideExact 2#usize)
 (rho : aspis_core.field.QM31) (last : transcript.Transcript Unit) :
 let p:=PreparedScratchReachability.output sem v gamma kappa alpha rho qs claim last
 ∀ j,j<22 → (NFW_PreparedPort.prepared p).queries.val[j]!.val<262144 := by
 change ∀ j,j<22 → qs.val[j]!.val<262144
 exact NLL_QueryCarrier.source hashv self row payload observed cuts qs after returned

set_option pp.proofs false
#print source
#print axioms source
end NLL_Tx1QueryCarrier
end
