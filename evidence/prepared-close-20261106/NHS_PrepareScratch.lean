import RPz7_SAP_Cuts
import NHS_ProducedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PrepareScratch
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge
/-- The returned scratch is the SAME mapped powers vector from that successful
preparation, for every incoming scratch and every admitted digest carrier. -/
theorem source (ops : Ops)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (p : verifier.Prepared)
 (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
   D pub proof hash none input=ok (.Ok p,scratch)) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch)) := by
 obtain ⟨stored,initial,expanded,y1,view,sem,read,expand,wide,same,verify,prepare⟩ :=
   SAP_Cuts.buffers ops B std D hash pub proof p input scratch success
 obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
   (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
   input scratch p prepare
 have model : AspisR1PublicPreparation.PreparedScratchModel.prepare NHL_PreparedScalars.actual
   (retainedDigest D) (retainedSem sem) (retainedView view) hash (mapArray retainedE input)=ok (.Ok out,rs) := prepared
 rw [NHL_QueryDomain.dictionary] at model
 have canonical := (NFW_PrepareQuery.domains NHL_PreparedScalars.actual.sampling
   (retainedDigest D) (retainedSem sem) (retainedView view) hash out rs (mapArray retainedE input) model).1
 rw [←scratchEq]
 have port : Tx1Q_Carriers.arr Tx1Q_Carriers.e (mapArray currentE rs)=
   NFW_PreparedPort.map NFW_PreparedPort.e rs := by
  apply Subtype.ext
  simp only [Tx1Q_Carriers.arr,mapArray,NFW_PreparedPort.map,List.map_map]
  rfl
 rw [port]
 exact canonical
#print axioms source
end AspisR1.NHS_PrepareScratch
