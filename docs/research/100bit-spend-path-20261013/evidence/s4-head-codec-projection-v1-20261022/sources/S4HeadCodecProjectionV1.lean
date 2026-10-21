import AeneasWordCodec
import R1ExactLeafFieldCodec
import R1ExactBaseProjection
import S4HeadFieldAlgebraRootV1
import S4C1M31SourceSliceV1
import S4LiteralHeadSumRootV1

set_option autoImplicit false

namespace AspisR1S4HeadCodecProjectionV1

open AspisR1.RetainedFieldByteCodec
open AspisR1.ExactBaseProjection
open AspisR1FastDotsHeadFieldAlgebraRootV1
open AspisR1S4C1M31SourceSliceV1
open AspisR1FastDotsLiteralHeadSumRootV1
open AspisR1FastDotsTailFieldProductRootV1

abbrev M31Value := AspisR1.RetainedFieldByteCodec.M31Value

def wordArray (bytes : AspisR1.RetainedFieldByteCodec.WordBytes) :
    Aeneas.Std.Array Aeneas.Std.U8 4#usize :=
  Aeneas.Std.Array.make 4#usize
    [AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 0),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 1),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 2),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 3)]

theorem rawByte_injective : Function.Injective AspisR1.ExtractedRecordByteValue.rawByte := by
  intro a b h
  apply Aeneas.Std.UScalar.eq_of_val_eq
  exact congrArg Fin.val h
open AspisWideTower

theorem raw_u32_of_encoded_m31 (x : AspisR1.ExactLeafFieldCodec.M31Exact) :
    (Aeneas.Std.core.num.U32.from_le_bytes
      (Aeneas.Std.Array.make 4#usize
        [AspisV8R19.SqueezeOracleBridge.encodeByte
            (AspisR1.RetainedFieldByteCodec.encodeM31LE
              (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x) 0),
         AspisV8R19.SqueezeOracleBridge.encodeByte
            (AspisR1.RetainedFieldByteCodec.encodeM31LE
              (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x) 1),
         AspisV8R19.SqueezeOracleBridge.encodeByte
            (AspisR1.RetainedFieldByteCodec.encodeM31LE
              (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x) 2),
         AspisV8R19.SqueezeOracleBridge.encodeByte
            (AspisR1.RetainedFieldByteCodec.encodeM31LE
              (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x) 3)]
      )).val =
      (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x).val := by
  change (AspisR1.AeneasWordCodec.aeneasWord
      (AspisR1.RetainedFieldByteCodec.encodeM31LE
        (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x))).val = _
  rw [AspisR1.AeneasWordCodec.aeneasWord_val_eq]
  have hround : AspisR1.RetainedFieldByteCodec.decodeWordLE
      (AspisR1.RetainedFieldByteCodec.encodeM31LE
        (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x)) =
      AspisR1.RetainedFieldByteCodec.m31AsRawWord
        (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x) := by
    change AspisR1.RetainedFieldByteCodec.decodeWordLE
      (AspisR1.RetainedFieldByteCodec.encodeWordLE
        (AspisR1.RetainedFieldByteCodec.m31AsRawWord
          (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x))) = _
    exact AspisR1.RetainedFieldByteCodec.decodeWordLE_encodeWordLE _
  simpa [AspisR1.RetainedFieldByteCodec.m31AsRawWord] using congrArg Fin.val hround

theorem embedded_encoded_m31 (x : AspisR1.ExactLeafFieldCodec.M31Exact) :
    embedM31 (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x).val = embed x := by
  have hEmbed : ((AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x).val :
      AspisR1.ExactLeafFieldCodec.M31Exact) = x := by
    have hv := congrArg ZMod.val
      (Equiv.apply_symm_apply
        AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.toEquiv x)
    change (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x).val = x.val at hv
    calc
      ((AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x).val :
          AspisR1.ExactLeafFieldCodec.M31Exact) = (x.val :
          AspisR1.ExactLeafFieldCodec.M31Exact) := congrArg
            (fun n : Nat => (n : AspisR1.ExactLeafFieldCodec.M31Exact)) hv
      _ = x := ZMod.natCast_zmod_val x
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;> simp [embedM31, embed, hEmbed]

theorem encoded_wordArray_raw (x : AspisR1.ExactLeafFieldCodec.M31Exact) :
    ((wordArray (AspisR1.RetainedFieldByteCodec.encodeM31LE
      (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm x))).val.map
      AspisR1.ExtractedRecordByteValue.rawByte) =
      AspisR1.ExactLeafFieldCodec.encodeM31 x := by
  have hrt (b : AspisR1.RetainedFieldByteCodec.Byte) :
      AspisR1.ExtractedRecordByteValue.rawByte
          (AspisV8R19.SqueezeOracleBridge.encodeByte b) = b := by
    change AspisV8R19.SqueezeOracleBridge.decodeByte
        (AspisV8R19.SqueezeOracleBridge.encodeByte b) = b
    exact AspisV8R19.SqueezeOracleBridge.byte_roundtrip b
  simp [wordArray, Aeneas.Std.Array.make,
    AspisR1.ExactLeafFieldCodec.encodeM31,
    AspisR1.ListFieldCodec.encodeM31Bytes, hrt]

theorem c1_m31_array_eq {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : AspisR1S4C1M31SourceSliceV1.C1)
    (c2 : AspisR1S4C1M31SourceSliceV1.C2) (slot : Fin 4) (term : Fin 26)
    (hbytes : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      AspisR1.MixedLeafEncoding.encodeC1 c1 ++
        AspisR1.MixedLeafEncoding.encodeC2 c2) :
    (⟨a.val.slice (120 * slot.val + 4 * term.val)
      (120 * slot.val + 4 * term.val + 4), by
        have hs := c1_m31_source_slice c1 c2 slot term hbytes
        have hlen := congrArg List.length hs
        simpa [List.length_map,
          AspisR1.ExactLeafFieldCodec.encodeM31_length] using hlen⟩ :
      Aeneas.Std.Array Aeneas.Std.U8 4#usize) =
      wordArray (AspisR1.RetainedFieldByteCodec.encodeM31LE
        (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm
          ((c1 slot).1 term))) := by
  apply Subtype.ext
  apply (List.map_injective_iff.mpr rawByte_injective)
  calc
    _ = AspisR1.ExactLeafFieldCodec.encodeM31 ((c1 slot).1 term) :=
      c1_m31_source_slice c1 c2 slot term hbytes
    _ = _ := (encoded_wordArray_raw ((c1 slot).1 term)).symm

theorem c1_m31_head_term {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : AspisR1S4C1M31SourceSliceV1.C1)
    (c2 : AspisR1S4C1M31SourceSliceV1.C2)
    (g : Aeneas.Std.Array Wide 29#usize) (slot : Fin 4) (term : Fin 26)
    (gamma : TowerWide) (wide : Wide)
    (hbytes : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      AspisR1.MixedLeafEncoding.encodeC1 c1 ++
        AspisR1.MixedLeafEncoding.encodeC2 c2)
    (hget : g.val[term.val]? = some wide)
    (hpow : wideDecoded wide = gamma ^ term.val) :
    headTermValue a g slot.val term.val = embed ((c1 slot).1 term) * gamma ^ term.val := by
  have hslice := c1_m31_source_slice c1 c2 slot term hbytes
  have hlen : (a.val.slice (120 * slot.val + 4 * term.val)
      (120 * slot.val + 4 * term.val + 4)).length = 4 := by
    have hh := congrArg List.length hslice
    simpa [List.length_map, AspisR1.ExactLeafFieldCodec.encodeM31_length] using hh
  have harray := c1_m31_array_eq c1 c2 slot term hbytes
  have hsliceEq : a.val.slice (slot.val * 120 + term.val * 4)
      (slot.val * 120 + term.val * 4 + 4) =
      a.val.slice (120 * slot.val + 4 * term.val)
        (120 * slot.val + 4 * term.val + 4) := by
    congr 1 <;> omega
  have hlen' : (a.val.slice (slot.val * 120 + term.val * 4)
      (slot.val * 120 + term.val * 4 + 4)).length = (4#usize).val := by
    rw [hsliceEq]
    simpa using hlen
  have harray' : (⟨a.val.slice (slot.val * 120 + term.val * 4)
      (slot.val * 120 + term.val * 4 + 4), hlen'⟩ :
      Aeneas.Std.Array Aeneas.Std.U8 4#usize) =
      wordArray (AspisR1.RetainedFieldByteCodec.encodeM31LE
        (AspisR1.RetainedExactLimbCodec.m31ResidueEquiv.symm
          ((c1 slot).1 term))) := by
    apply Subtype.ext
    exact hsliceEq.trans (congrArg Subtype.val harray)
  have hparse := congrArg Aeneas.Std.core.num.U32.from_le_bytes harray'
  simp only [headTermValue, hget]
  rw [dif_pos hlen']
  rw [hparse]
  unfold wordArray
  rw [raw_u32_of_encoded_m31, embedded_encoded_m31, hpow, mul_comm]

end AspisR1S4HeadCodecProjectionV1
