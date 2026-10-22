import S9ActualFromLimbsOwnedMapV1
import AspisR1S9FieldOwnedV1.Funs

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9ActualFieldTypesCutV1

@[global_simps, irreducible]
def field.wide_exact.WideExact.BYTE_LEN : Std.Usize := 32#usize


def field.wide_exact.WideExact.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.wide_exact.WideExact) := do
  let i := Slice.len bytes
  if i != field.wide_exact.WideExact.BYTE_LEN
  then ok none
  else
    let i1 ← Slice.index_usize bytes 0#usize
    let i2 ← Slice.index_usize bytes 1#usize
    let i3 ← Slice.index_usize bytes 2#usize
    let i4 ← Slice.index_usize bytes 3#usize
    let i5 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i1, i2, i3, i4 ]))
    let i6 ← Slice.index_usize bytes 4#usize
    let i7 ← Slice.index_usize bytes 5#usize
    let i8 ← Slice.index_usize bytes 6#usize
    let i9 ← Slice.index_usize bytes 7#usize
    let i10 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i6, i7, i8, i9 ]))
    let i11 ← Slice.index_usize bytes 8#usize
    let i12 ← Slice.index_usize bytes 9#usize
    let i13 ← Slice.index_usize bytes 10#usize
    let i14 ← Slice.index_usize bytes 11#usize
    let i15 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i11, i12, i13, i14 ]))
    let i16 ← Slice.index_usize bytes 12#usize
    let i17 ← Slice.index_usize bytes 13#usize
    let i18 ← Slice.index_usize bytes 14#usize
    let i19 ← Slice.index_usize bytes 15#usize
    let i20 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i16, i17, i18, i19 ]))
    let i21 ← Slice.index_usize bytes 16#usize
    let i22 ← Slice.index_usize bytes 17#usize
    let i23 ← Slice.index_usize bytes 18#usize
    let i24 ← Slice.index_usize bytes 19#usize
    let i25 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i21, i22, i23, i24 ]))
    let i26 ← Slice.index_usize bytes 20#usize
    let i27 ← Slice.index_usize bytes 21#usize
    let i28 ← Slice.index_usize bytes 22#usize
    let i29 ← Slice.index_usize bytes 23#usize
    let i30 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i26, i27, i28, i29 ]))
    let i31 ← Slice.index_usize bytes 24#usize
    let i32 ← Slice.index_usize bytes 25#usize
    let i33 ← Slice.index_usize bytes 26#usize
    let i34 ← Slice.index_usize bytes 27#usize
    let i35 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i31, i32, i33, i34 ]))
    let i36 ← Slice.index_usize bytes 28#usize
    let i37 ← Slice.index_usize bytes 29#usize
    let i38 ← Slice.index_usize bytes 30#usize
    let i39 ← Slice.index_usize bytes 31#usize
    let i40 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i36, i37, i38, i39 ]))
    field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ i5, i10, i15, i20, i25, i30, i35, i40 ])


end AspisR1S9ActualFieldTypesCutV1

namespace AspisR1S9ActualFromBytesOwnedMapV1

open AspisR1S9ActualFromLimbsOwnedMapV1

private theorem mapResult_bind {A B C : Type} (f : B → C)
    (m : Result A) (k : A → Result B) :
    mapResult f (do let x ← m; k x) = (do let x ← m; mapResult f (k x)) := by
  cases m <;> rfl

/-- The copied attempt7 byte decoder commutes with the retained owned decoder,
using the actual `from_limbs` carrier map after the same byte reads and lifts. -/
theorem actual_from_le_bytes_maps_to_owned (bytes : Slice U8) :
    mapOptionResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
      (AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_le_bytes bytes) =
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes := by
  unfold AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_le_bytes
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes
  simp only [mapOptionResult,
    AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.BYTE_LEN]
  rw [mapResult_ite]
  split_ifs with hlen
  · simp only [mapResult, Option.map_none]
  · have hm (limbs : Array U32 8#usize) :
        mapResult (Option.map AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned)
          (AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_limbs limbs) =
        AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs :=
      AspisR1S9ActualFromLimbsOwnedMapV1.actual_from_limbs_maps_to_owned limbs
    simp only [mapResult_bind, hm]

#print axioms actual_from_le_bytes_maps_to_owned

end AspisR1S9ActualFromBytesOwnedMapV1
