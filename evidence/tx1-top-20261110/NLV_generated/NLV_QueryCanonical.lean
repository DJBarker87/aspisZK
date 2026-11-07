import NHS_PrepareFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_QueryCanonical
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
/-- A reached successful PREPARE output carries canonical query words from
its OWN constructor. This is a model implication, not a native success premise
in a row root. The parent must obtain this success at its actual occurrence. -/
theorem source (ops : Ops)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (p : verifier.Prepared)
 (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
 D pub proof hash none input=ok (.Ok p,scratch)) :
 ∀ j,j<22 → p.queries.val[j]!.val<262144 := by
 obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
   SAP_OpeningCuts.opening ops B std D hash pub proof p input scratch success
 have variant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
   change retainedVariant view.variant=_
   rw [sourceView_variant proof expanded y1 view wide]
   rfl
 have shape := SAP_OpeningShape.fields (retainedDigest D) (retainedSem sem) (retainedView view)
  hash out rs variant reached
 rw [←outEq]
 change ∀ j,j<22 → out.queries.val[j]!.val<262144
 intro j hj
 have length : out.queries.val.length=22 := out.queries.property
 have within : j<out.queries.val.length := by omega
 have bound := shape.2.2.2.1 ⟨j,hj⟩
 simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem within,Option.getD_some] using bound
#print axioms source
end AspisR1.NLV_QueryCanonical
end
