import FourDotsCurrentQmParserRootV1
import ActualDecodeKStrictQM31Parser
import S4TailSlotEmbeddingV1
import S4TailSlotByteProjectionsV1
import FourDotsActualTailParserRootV1
import R1ExactLeafFieldCodec
import PublicExtractedRawBridge431

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailParserEmbeddingV1
open AspisR1.RetainedFieldByteCodec
open AspisR1.ExactLeafFieldCodec

abbrev QM := AspisR1FastDotsCurrentQmParserRootV1.QM
abbrev Ops := AspisR1FastDotsCurrentQmParserRootV1.Ops

private theorem of_arrayBytes16 (arr : Array U8 16#usize) :
    List.ofFn (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) =
      arr.val.map AspisR1.ExtractedRecordByteValue.rawByte := by
  calc
    List.ofFn (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) =
        List.ofFn (fun i : Fin 16 => AspisR1.ExtractedRecordByteValue.rawByte
          (arr.val[i.val]'(by
            have hlen : arr.val.length = 16 := by simpa using arr.property
            rw [hlen]
            exact i.isLt))) := by
      congr 1
    _ = arr.val.map AspisR1.ExtractedRecordByteValue.rawByte :=
      AspisR1PublicSerializer.RawBridge431.ofFn_map_getElem arr.val 16
        (by simpa using arr.property) AspisR1.ExtractedRecordByteValue.rawByte

/-- A successful installed current QM31 parser over bytes encoding an exact
retained QM31 value returns a current carrier with the same wide embedding. -/
theorem parser_success_exact_embedding
    (ops : Ops) (arr : Array U8 16#usize) (q : QM)
    (x : AspisV8R15.ExactTowerBase.QM31Exact)
    (hparse : (AspisR1FastDotsCurrentQmParserRootV1.withCurrentQmParser ops).qm31FromBytes
      (Array.to_slice arr) = .ok (some q))
    (hbytes : arr.val.map AspisR1.ExtractedRecordByteValue.rawByte = encodeQM31 x) :
    AspisR1FastDotsTailLiteralProductsRootV1.embedQM q =
      (algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact) x := by
  obtain ⟨limbs, _hdecode, hq, hlimbs, _h0, _h1, _h2, _h3⟩ :=
    AspisR1FastDotsCurrentQmParserRootV1.installed_parser_success_strict ops arr q hparse
  have hlist : List.ofFn (encodeQM31LE limbs) = encodeQM31 x := by
    calc
      List.ofFn (encodeQM31LE limbs) =
          List.ofFn (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) :=
        congrArg List.ofFn hlimbs
      _ = arr.val.map AspisR1.ExtractedRecordByteValue.rawByte := of_arrayBytes16 arr
      _ = encodeQM31 x := hbytes
  have hfun : encodeQM31LE limbs = encodeQM31LE
      (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x) := by
    have hlist' : List.ofFn (encodeQM31LE limbs) =
        List.ofFn (encodeQM31LE (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x)) := by
      simpa [encodeQM31, AspisR1.ExactLeafFieldCodec.encodeQM31,
        AspisR1.ListFieldCodec.encodeQM31Bytes] using hlist
    exact List.ofFn_injective hlist'
  have hlimbeq : limbs = AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x := by
    have h := congrArg decodeQM31LE hfun
    rw [decodeQM31LE_encodeQM31LE, decodeQM31LE_encodeQM31LE] at h
    exact Option.some.inj h
  rw [hq, AspisR1FastDotsTailSlotEmbeddingV1.current_qm_embedding]
  rw [hlimbeq]
  exact congrArg (algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact)
    (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.apply_symm_apply x)
end AspisR1FastDotsTailParserEmbeddingV1
