import R1Z.PV_Src_PublicHeader

/-! PublicCorr reduced to its remaining primitive root/frontier facts. These
are pure source obligations, not effects and not newly discharged premises. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PublicParts
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
variable {K : Type} [Field K] [CharP K 2147483647]

theorem reference_parts (roots : BuilderRecordsReference.Roots) (i : Input)
    (snapshot : i.compiled.public_statement.live_snapshot = i.snapshot)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (empty : ∀ l : Fin 20, DigestLift (roots.val[l.val]!) (emptyRootK (K := K) l))
    (emptyCanon : ∀ l : Fin 20, Canon8 roots.val[l.val]!) :
    PubCorr (PV_Src_PublicHeader.publicRecord roots i) (PV_Src_PublicHeader.publicInput (K := K) i) where
  variant := PV_Src_PublicHeader.variant roots i
  asset := PV_Src_PublicHeader.asset roots i
  next := PV_Src_PublicHeader.next roots i snapshot
  frontier := PV_Src_PublicHeader.frontier roots i snapshot
  empty := by
    intro l
    change DigestLift ((BuilderRecordsPublic.empty20 roots).val[l.val]!) _
    rw [BuilderRecordsPublic.empty20,BuilderRecordsArray.tabulate_get _ _ _ (by simpa using l.isLt)]
    exact empty l
  frontierCanon := frontier
  emptyCanon := by
    intro l
    change Canon8 ((BuilderRecordsPublic.empty20 roots).val[l.val]!)
    rw [BuilderRecordsPublic.empty20,BuilderRecordsArray.tabulate_get _ _ _ (by simpa using l.isLt)]
    exact emptyCanon l

theorem dynamic_parts [ExternalLinear] (i : Input)
    (success : @run _ PV_Src_RecordDynamic.dictionary i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (empty : ∀ roots, pair_trace.pair_empty_roots = ok roots →
      ∀ l : Fin 20, DigestLift (roots.val[l.val]!) (emptyRootK (K := K) l))
    (emptyCanon : ∀ roots, pair_trace.pair_empty_roots = ok roots →
      ∀ l : Fin 20, Canon8 roots.val[l.val]!)
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords PV_Src_RecordDynamic.dictionary i = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (PV_Src_NativeInput.publicInput i))) := by
  obtain ⟨roots,hroots,he⟩ := PV_Src_RecordDynamicResult.returned i r hr
  subst r
  have hs := @PV_Src_ReturnedSnapshot.returned_snapshot _ PV_Src_RecordDynamic.dictionary
    i.witness (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  exact reference_parts roots i hs frontier (empty roots hroots) (emptyCanon roots hroots)

#print axioms reference_parts
#print axioms dynamic_parts
end R1Z.PV_Src_PublicParts
