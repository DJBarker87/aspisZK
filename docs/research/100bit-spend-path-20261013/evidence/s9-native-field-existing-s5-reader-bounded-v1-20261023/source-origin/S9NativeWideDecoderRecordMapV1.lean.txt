import AspisR1S9ProductionPairCutV1.Funs
import S9OwnedFromBytesMapV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeWideDecoderRecordMapV1
abbrev NativeW := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
abbrev OwnedW := AspisR1S9FieldOwnedV1.field.wide_exact.WideExact
abbrev RecordW := AspisR1RecordParser.field.wide_exact.WideExact
open AspisR1S9OwnedFromLimbsMapV1 (mapResult mapOptionResult mapResult_ite)

def toOwnedCM (q : AspisR1S9ProductionPairCutV1.aspis_core.field.CM31) : AspisR1S9FieldOwnedV1.field.CM31 := ⟨q.a,q.b⟩
def toOwnedQM (q : AspisR1S9ProductionPairCutV1.aspis_core.field.QM31) : AspisR1S9FieldOwnedV1.field.QM31 :=
  ⟨toOwnedCM q.c0,toOwnedCM q.c1⟩
def toOwned (w : NativeW) : OwnedW := ⟨toOwnedQM w.c0,toOwnedQM w.c1⟩
def toRecord (w : NativeW) : RecordW := AspisR1S9OwnedFromLimbsMapV1.wideToParser (toOwned w)

/-- Actual native strict limb checks, with only nominal output carrier copied. -/
theorem native_limbs_maps_owned (limbs : Array U32 8#usize) :
    mapOptionResult toOwned
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_limbs limbs) =
      AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs := by
  simp [AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_limbs,
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs,
    AspisR1S9ProductionPairCutV1.aspis_core.field.P,AspisR1S9FieldOwnedV1.field.P,
    mapOptionResult,mapResult_ite,toOwned,toOwnedQM,toOwnedCM,Array.index_usize] <;>
    simp [mapResult,toOwned,toOwnedQM,toOwnedCM]

private theorem mapResult_bind {A B C : Type} (f : B → C) (m : Result A) (next : A → Result B) :
    mapResult f (do let x ← m; next x) = (do let x ← m; mapResult f (next x)) := by
  cases m <;> rfl

/-- Complete Result map of the CURRENT transparent native byte decoder.
Length guard, all32 ordered byte reads and every failure/None are preserved. -/
theorem native_bytes_maps_owned (bytes : Slice U8) :
    mapOptionResult toOwned
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_le_bytes
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes
  simp only [mapOptionResult,
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.BYTE_LEN]
  rw [mapResult_ite]
  split_ifs with hlen
  · simp only [mapResult,Option.map_none]
  · have hm (limbs : Array U32 8#usize) :
        mapResult (Option.map toOwned)
          (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_limbs limbs) =
          AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs := native_limbs_maps_owned limbs
    simp only [mapResult_bind,hm]

private theorem maps_comp (m : Result (Option NativeW)) :
    mapOptionResult AspisR1S9OwnedFromLimbsMapV1.wideToParser (mapOptionResult toOwned m) =
      mapOptionResult toRecord m := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok o => cases o <;> rfl

/-- Reuses the existing owned→RecordParser proof on the same bytes. -/
theorem native_bytes_maps_record (bytes : Slice U8) :
    mapOptionResult toRecord
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes := by
  rw [←maps_comp,native_bytes_maps_owned]
  exact AspisR1S9OwnedFromBytesMapV1.from_le_bytes_maps bytes

#print axioms native_limbs_maps_owned
#print axioms native_bytes_maps_owned
#print axioms native_bytes_maps_record
end AspisR1S9NativeWideDecoderRecordMapV1
