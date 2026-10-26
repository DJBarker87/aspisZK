import R1Z.PV_Src_RecordDynamicResult
import R1Z.PV_Src_ReturnedSnapshot

/-! Pure publicCorr projections. The source constructor fixes the variant
and asset; successful compilation fixes the snapshot index and frontier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PublicHeader
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
variable {K : Type} [Field K] [CharP K 2147483647]

def publicRecord (roots : BuilderRecordsReference.Roots) (i : Input) :=
  PV_Src_Forest_PrimitiveArguments.wordPublic (PV_Src_RecordReference.returned roots i).p

def publicInput (i : Input) :=
  mapPub (K := K) (PV_Src_Public.canonicalPublic (PV_Src_NativeInput.publicInput i))

theorem variant (roots : BuilderRecordsReference.Roots) (i : Input) :
    (publicRecord roots i).variant = (publicInput (K := K) i).variant := by
  cases hr : i.request <;> simp only [publicRecord,publicInput,PV_Src_RecordReference.returned,
      PV_Src_RecordReference.publicRecord,BuilderRecordsReference.publicRecord,
      PV_Src_RecordReference.snapshot,
      PV_Src_Forest_PrimitiveArguments.wordPublic,PV_Src_NativeInput.publicInput,
      PV_Src_NativeInput.forestPublic,PV_Src_NativeInput.recipient,hr,
      PV_Src_NativeInput.transition,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] <;> rfl

theorem asset (roots : BuilderRecordsReference.Roots) (i : Input) :
    liftU (K := K) (publicRecord roots i).asset = (publicInput (K := K) i).assetId := by
  cases hr : i.request <;>
    simp only [publicRecord,publicInput,PV_Src_RecordReference.returned,
      PV_Src_RecordReference.publicRecord,BuilderRecordsReference.publicRecord,
      PV_Src_Forest_PrimitiveArguments.wordPublic,PV_Src_NativeInput.publicInput,
      PV_Src_NativeInput.forestPublic,PV_Src_NativeInput.recipient,hr,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub,liftU,map_natCast]

theorem next (roots : BuilderRecordsReference.Roots) (i : Input)
    (hs : i.compiled.public_statement.live_snapshot = i.snapshot) :
    (publicRecord roots i).nextPairIndex = (publicInput (K := K) i).nextPairIndex := by
  cases hr : i.request <;> simp only [publicRecord,publicInput,PV_Src_RecordReference.returned,
      PV_Src_RecordReference.publicRecord,BuilderRecordsReference.publicRecord,
      PV_Src_RecordReference.snapshot,
      PV_Src_Forest_PrimitiveArguments.wordPublic,PV_Src_NativeInput.publicInput,
      PV_Src_NativeInput.forestPublic,PV_Src_NativeInput.recipient,hr,
      PV_Src_NativeInput.transition,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs]

theorem frontier (roots : BuilderRecordsReference.Roots) (i : Input)
    (hs : i.compiled.public_statement.live_snapshot = i.snapshot) (l : Fin 20) :
    DigestLift ((publicRecord roots i).frontier.val[l.val]!)
      ((publicInput (K := K) i).snapshotFrontier l) := by
  intro lane
  cases hr : i.request <;> simp only [publicRecord,publicInput,PV_Src_RecordReference.returned,
      PV_Src_RecordReference.publicRecord,BuilderRecordsReference.publicRecord,
      PV_Src_RecordReference.snapshot,
      PV_Src_Forest_PrimitiveArguments.wordPublic,PV_Src_NativeInput.publicInput,
      PV_Src_NativeInput.forestPublic,PV_Src_NativeInput.recipient,hr,
      PV_Src_NativeInput.transition,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs] <;> simp only [digK,liftU,map_natCast]

#print axioms variant
#print axioms asset
#print axioms next
#print axioms frontier
end R1Z.PV_Src_PublicHeader
