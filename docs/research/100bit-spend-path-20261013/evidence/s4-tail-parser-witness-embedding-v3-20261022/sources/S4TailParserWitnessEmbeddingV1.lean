import S4TailParserEmbeddingV1
import S4TailSlotByteProjectionsV1
import FourDotsActualCallbackParserRootV1
import S4HeadTailSharedWitnessRootV2
import FourDotsActualTailBodyTraceRootV1
import FourDotsCurrentQmParserRootV1
import R1MixedLeafEncoding

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailParserEmbeddingV1
open AspisR1.RetainedFieldByteCodec
open AspisR1.ExactLeafFieldCodec
open AspisR1.MixedLeafEncoding

abbrev Usize := Aeneas.Std.Usize
abbrev U8 := Aeneas.Std.U8
abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2
abbrev TailOps := AspisR1FastDotsActualCallbackTailTraceRootV1.Ops
abbrev TailWide := AspisR1FastDotsActualCallbackTailTraceRootV1.Wide
abbrev TailState := AspisR1FastDotsActualCallbackTailTraceRootV1.Tail
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact


private theorem parser_slice_exact_embedding_local
    (ops : AspisR1FastDotsCurrentQmParserRootV1.Ops) (bytes : Slice U8) (q : QM)
    (x : QMExact) (hlen : bytes.val.length = 16)
    (hbinding : ops.qm31FromBytes = AspisR1FastDotsCurrentQmParserRootV1.parser)
    (hparse : ops.qm31FromBytes bytes = .ok (some q))
    (hbytes : bytes.val.map AspisR1.ExtractedRecordByteValue.rawByte = encodeQM31 x) :
    AspisR1FastDotsTailLiteralProductsRootV1.embedQM q =
      (algebraMap QMExact AspisWideTower.WideExact) x := by
  have hp : (AspisR1FastDotsCurrentQmParserRootV1.withCurrentQmParser ops).qm31FromBytes
      (Array.to_slice (AspisR1FastDotsActualTailParserRootV1.frame bytes hlen)) =
        .ok (some q) := by
    rw [AspisR1FastDotsCurrentQmParserRootV1.parser_binding,
      AspisR1FastDotsActualTailParserRootV1.frame_to_slice]
    rw [← hbinding]
    exact hparse
  have hb : (AspisR1FastDotsActualTailParserRootV1.frame bytes hlen).val.map
      AspisR1.ExtractedRecordByteValue.rawByte = encodeQM31 x := by
    simpa [AspisR1FastDotsActualTailParserRootV1.frame] using hbytes
  exact parser_success_exact_embedding ops
    (AspisR1FastDotsActualTailParserRootV1.frame bytes hlen) q x hp hb

private theorem option_unwrap_success_local {A : Type} (opt : Option A) (x : A)
    (h : core.option.Option.unwrap opt = .ok x) : opt = some x := by
  cases opt with
  | none => simp only [core.option.Option.unwrap, Result.ofOption] at h; cases h
  | some y => have hy : y=x := Result.ok.inj (by
      simpa only [core.option.Option.unwrap, Result.ofOption] using h); subst y; rfl

/-- The first source tail parser result is tied to the exact selected C1 slot
encoding and therefore to its exact wide embedding. -/
theorem first_query_exact_embedding
    (ops : AspisR1FastDotsHeadTailSharedWitnessRootV2.Ops)
    (a : Array U8 608#usize) (slot : Usize) (slotFin : Fin 4) (q : QM)
    (c1 : C1) (c2 : C2)
    (hslot : slot.val = slotFin.val)
    (hopening : a.val.map AspisR1.ExtractedRecordByteValue.rawByte = encodeC1 c1 ++ encodeC2 c2)
    (hbinding : ops.qm31FromBytes = AspisR1FastDotsCurrentQmParserRootV1.parser)
    (hfirst : AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q) :
    AspisR1FastDotsTailLiteralProductsRootV1.embedQM q =
      (algebraMap QMExact AspisWideTower.WideExact) ((c1 slotFin).2) := by
  obtain ⟨offset,start,finish,bytes,hmul,hstart,hfinish,hslice,hparse⟩ := hfirst
  have hoff : offset.val = slot.val * 120 := by
    have h := UScalar.mul_equiv slot 120#usize
    change UScalar.mul slot 120#usize = .ok offset at hmul
    rw [hmul] at h
    exact h.2.1
  have hsval : start.val = offset.val + 104 := by
    have h := UScalar.add_equiv offset 104#usize
    rw [hstart] at h
    exact h.2.1
  have hfval : finish.val = offset.val + 120 := by
    have h := UScalar.add_equiv offset 120#usize
    rw [hfinish] at h
    exact h.2.1
  have hspan : finish.val = start.val + 16 := by omega
  obtain ⟨hlen,hcontent⟩ :=
    AspisR1FastDotsActualCallbackParserRootV1.indexed_sixteen_byte_frame
      a start finish bytes hspan hslice
  have hbytes : bytes.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      encodeQM31 ((c1 slotFin).2) := by
    rw [hcontent, hsval, hfval, hoff, hslot]
    simpa [Nat.mul_comm] using
      AspisR1FastDotsTailSlotByteProjectionsV1.c1_tail_source_slice
        c1 c2 slotFin hopening
  exact parser_slice_exact_embedding_local ops bytes q ((c1 slotFin).2)
    hlen hbinding hparse hbytes

/-- Each successful actual tail source read/parser result is the exact C2 lane
selected by its source `slot` and iterator `term`. -/
theorem contribution_exact_embedding
    (ops : TailOps)
    (a : Array U8 608#usize) (g : Array TailWide 29#usize)
    (slot : Usize) (slotFin : Fin 4) (termFin : Fin 2)
    (iter iter' : AspisR1FastDotsActualTailBodyTraceRootV1.Range)
    (old next : TailState)
    (c : AspisR1FastDotsActualTailBodyTraceRootV1.Contribution)
    (c1 : C1) (c2 : C2)
    (hslot : slot.val = slotFin.val) (hterm : c.term.val = termFin.val)
    (hopening : a.val.map AspisR1.ExtractedRecordByteValue.rawByte = encodeC1 c1 ++ encodeC2 c2)
    (hbinding : ops.qm31FromBytes = AspisR1FastDotsCurrentQmParserRootV1.parser)
    (hw : AspisR1FastDotsActualTailBodyTraceRootV1.InputWitness
      ops a g slot iter iter' old next c) :
    AspisR1FastDotsTailLiteralProductsRootV1.embedQM c.scalar =
      (algebraMap QMExact AspisWideTower.WideExact) ((c2 slotFin) termFin) := by
  obtain ⟨slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
    hnext,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩ := hw
  have hslot32 : slot32.val = slot.val * 32 := by
    have h := UScalar.mul_equiv slot 32#usize
    change UScalar.mul slot 32#usize = .ok slot32 at h0
    rw [h0] at h
    exact h.2.1
  have hbase : base480.val = 480 + slot32.val := by
    have h := UScalar.add_equiv 480#usize slot32
    rw [h1] at h
    exact h.2.1
  have hterm16 : term16.val = c.term.val * 16 := by
    have h := UScalar.mul_equiv c.term 16#usize
    change UScalar.mul c.term 16#usize = .ok term16 at h2
    rw [h2] at h
    exact h.2.1
  have hoff : offset.val = base480.val + term16.val := by
    have h := UScalar.add_equiv base480 term16
    rw [h3] at h
    exact h.2.1
  have hfin : finish.val = offset.val + 16 := by
    have h := UScalar.add_equiv offset 16#usize
    rw [h5] at h
    exact h.2.1
  obtain ⟨hlen,hcontent⟩ :=
    AspisR1FastDotsActualCallbackParserRootV1.indexed_sixteen_byte_frame
      a offset finish c.bytes (by omega) hslice
  have hbytes : c.bytes.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      encodeQM31 ((c2 slotFin) termFin) := by
    rw [hcontent, hfin, hoff, hbase, hslot32, hterm16, hslot, hterm]
    simpa [Nat.mul_comm] using
      AspisR1FastDotsTailSlotByteProjectionsV1.c2_lane_source_slice
        c1 c2 slotFin termFin hopening
  have hopt : optQ = some c.scalar := option_unwrap_success_local optQ c.scalar hunwrap
  have hparse' : ops.qm31FromBytes c.bytes = .ok (some c.scalar) := by
    rw [hopt] at hparse
    exact hparse
  exact parser_slice_exact_embedding_local ops c.bytes c.scalar ((c2 slotFin) termFin)
    hlen hbinding hparse' hbytes

#print axioms first_query_exact_embedding
#print axioms contribution_exact_embedding
end AspisR1FastDotsTailParserEmbeddingV1
