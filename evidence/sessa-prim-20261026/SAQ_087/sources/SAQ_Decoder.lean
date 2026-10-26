import SAQ_RecordDecode
import SAQ_LineQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Decoder
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices

def read (bytes : Slice U8) (i : Usize) : Result SAQ_WideABI.E := do
  let start ← 32#usize*i
  let finish ← start+32#usize
  let selected ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    bytes {start:=start,«end»:=finish}
  let decoded ← AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected
  let raw ← core.option.Option.unwrap decoded
  ok (SAQ_RecordDecode.fromRecord raw)

theorem law (bytes : Slice U8) (i : Usize) (z : SAQ_WideABI.E)
    (hi : i.val<4) (length : bytes.val.length=128) (run : read bytes i=ok z) :
    FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice (bytesOf bytes.val) (32*i.val) 32)=
      some (CheckpointBytes5Output.ofE z) := by
  obtain ⟨start,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨finish,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨selected,selectedCall,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨decoded,decodedCall,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases decoded with
  | none => simp [core.option.Option.unwrap] at run
  | some raw =>
    simp only [core.option.Option.unwrap,bind_tc_ok] at run
    have same : SAQ_RecordDecode.fromRecord raw=z := Result.ok.inj run
    subst z
    change UScalar.mul (32#usize) i=ok start at hs
    change UScalar.add start (32#usize)=ok finish at hf
    have hstart := UScalar.mul_equiv (32#usize) i
    rw [hs] at hstart
    have sv : start.val=32*i.val := hstart.2.1
    have hfinish := UScalar.add_equiv start (32#usize)
    rw [hf] at hfinish
    have fv : finish.val=start.val+32 := hfinish.2.1
    have selectedEq : selected=sub bytes start finish := Result.ok.inj
      (selectedCall.symm.trans (range_total bytes start finish (by omega) (by rw [length]; omega)))
    have decoded := SAQ_RecordDecode.successful selected raw decodedCall
    rw [selectedEq,bytes_sub,fv,sv] at decoded
    simpa only [Nat.add_sub_cancel_left] using decoded

def install (ops : SAQ_Query.Ops) : SAQ_Query.Ops :=
  {SAQ_LineQuery.install ops with op21 := read}

theorem primitives (ops : SAQ_Query.Ops) : Port5Q1_QueryPorts.SessionAPrimitives (install ops) := by
  refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_⟩
  · exact ⟨SAQ_MixedSource.mulE_exact,SAQ_Arithmetic.add_exact,SAQ_Arithmetic.mulK_exact⟩
  · exact ⟨(SAQ_Query.m31 ops).multiply,(SAQ_Query.m31 ops).double,
      (SAQ_Query.m31 ops).one,(SAQ_Query.m31 ops).subtract⟩
  · exact ⟨law⟩
  · intro alpha values inverse z run
    exact (SAQ_LineQuery.exact_line alpha values inverse z run).1
  · intro alpha values inverse z run
    exact (SAQ_LineQuery.exact_line alpha values inverse z run).2

#print axioms law
#print axioms primitives
end AspisR1.SAQ_Decoder
end
