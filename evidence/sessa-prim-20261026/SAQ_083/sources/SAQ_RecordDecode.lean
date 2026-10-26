import SAQ_RecordStrictCodec
import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_RecordDecode
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordStrictCodec
abbrev R := AspisR1RecordParser.field.wide_exact.WideExact

def fromRecord (x : R) : SAQ_WideABI.E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem residue_cast (x : RetainedFieldByteCodec.M31Value) :
    RetainedExactLimbCodec.m31ResidueEquiv x =
      (x.val : AspisV8R15.ExactTowerBase.M31Exact) := by
  apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
  change x.val = (x.val : ZMod AspisV8R15.ExactTowerBase.P).val
  rw [ZMod.val_natCast_of_lt x.isLt]

theorem packed_value (arr : Array U8 32#usize)
    (canonical : ∀ i : Fin 8, (wordLE arr i).val<2147483647) :
    WideExactLimbCodec.pairExactEquiv (canonicalLimbs arr canonical) =
      CheckpointBytes5Output.ofE (fromRecord (ExtractedRecordLimbCanonicality.packed
        (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
        (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7))) := by
  rw [SAQ_WideABI.w_decode,WideExactLimbCodec.pairExactEquiv_apply]
  ext <;> simp [WideExactLimbCodec.pairToExact,RetainedExactLimbCodec.qm31ExactLimbEquiv,
    RetainedExactLimbCodec.limbsToQM31Exact,canonicalLimbs,canonicalWords,residue_cast,
    fromRecord,ExtractedRecordLimbCanonicality.packed,SAQ_WideABI.toW,SAQ_WideABI.toQ,
    AspisR1CurrentWide.Proof.decodeWide,AspisR1CurrentWide.Proof.decodeQM,
    AspisR1CurrentWide.Proof.toQM,AspisR1CurrentWide.Proof.toCM,ExtractedCurrentQM31Exact.decode]

theorem successful (bytes : Slice U8) (w : R)
    (h : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes=ok (some w)) :
    FoldedLeafCodec.decodeWide (MultiproofConeCanonical.bytesOf bytes.val)=
      some (CheckpointBytes5Output.ofE (fromRecord w)) := by
  obtain ⟨_,arr,hs,hc,hp⟩ := slice_success bytes w h
  have same : arr.val=bytes.val := congrArg Slice.val hs
  rw [←same,hp]
  have lists : List.ofFn (arrayBytes arr)=MultiproofConeCanonical.bytesOf arr.val := arrayBytes_list arr
  rw [←lists,FoldedLeafCodec.decodeWide,ListFieldCodec.fixedBytes?_ofFn,strict_decode arr hc]
  exact congrArg some (packed_value arr hc)

#print axioms residue_cast
#print axioms packed_value
#print axioms successful
end AspisR1.SAQ_RecordDecode
end
